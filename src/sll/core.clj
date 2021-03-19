(ns sll.core
  (:gen-class))

;---------------------------------------------------------
; Protocols
;---------------------------------------------------------

(defprotocol Syntax-Operations
  (apply-subst [exp s])
  (id-subst [exp]))

(defprotocol Map-Results
  (map-result [step f]))

(defprotocol Eval-Step
  (eval-step [expr prog]))

(defprotocol Meta-Eval-Step
  (meta-eval-step [expr prog]))

(defprotocol DefLookup
  "lookup of definitions in a program"
  (is-f [def name] "whether a `def` is an f-definition with name `name`")
  (is-g [def name] "whether a `def` is a g-definition with name `name`")
  (is-g-pat [def name ctr-name] "whether a `def` is a g-definition with name `name` for `ctr-name`"))

(defprotocol BuildEvalTree
  "build an evaluation tree via steps"
  (grow-eval-tree [step prog expr]))
(defprotocol BuildProcessTree
  "build a process tree via steps"
  (grow-process-tree [step prog expr id]))
(defprotocol BuildPerfectProcessTree
  "make steps perfect"
  (mk-perfect [step]))
(extend-type Object
  BuildPerfectProcessTree
  (mk-perfect [step] step))

(defprotocol EvalEvalTree
  "evaluate an evaluation tree"
  (eval-tree [tree]))

(defprotocol URA
  "defs for traversing a process tree"
  (ura-step [tree subst out] "performs an URA step for a current (first) tree in the queue"))

(defprotocol Unparse
  "unparses an expression into s-form"
  (unparse [e]))

;---------------------------------------------------------
; Logic
;---------------------------------------------------------

(defn remap [sub1 sub2]
  "apply sub2 to values of sub1"
  (zipmap (keys sub1) (map #(apply-subst %1 sub2) (vals sub1))))

(defn perfect-meta-stepper [prog e]
  (mk-perfect (meta-eval-step e prog)))

(defn program-fdef [program f-name]
  (first (filter #(is-f %1 f-name) program)))

(defn program-gdefs [program g-name]
  (seq (filter #(is-g %1 g-name) program)))

(defn program-gdef [program g-name ctr-name]
  (first (filter #(is-g-pat %1 g-name ctr-name) program)))

(defn build-eval-tree [prog expr]
  (grow-eval-tree (eval-step expr prog) prog expr))

(defn build-process-tree [prog expr]
  (grow-process-tree (perfect-meta-stepper prog expr) prog expr '()))

(defn ura [prog in out]
  (letfn [(traverse [queue]
            (if (empty? queue) '()
                (let [[[subst tree] & queue] queue {answer :answer delta :delta} (ura-step tree subst out)]
                  (concat answer (traverse (concat queue delta))))))]
    (traverse (list [(id-subst in) (build-process-tree prog in)]))))

;---------------------------------------------------------
; Trees and steps
;---------------------------------------------------------

(defrecord URA-Step [answer delta])

(defrecord Process-leaf [id expr]
  URA
  (ura-step [_ subst out] (->URA-Step (if (= expr out) (list subst)) '())))
(defrecord Process-node-transient [id expr tree]
  URA
  (ura-step [_ subst out] (->URA-Step nil (list [subst tree]))))
(defrecord Process-node-variants  [id expr variants]
  URA
  (ura-step [_ subst out] (->URA-Step nil (map (fn [[s t]] [(remap subst s) t]) variants))))

(defrecord Eval-Leaf [expr]
  EvalEvalTree
  (eval-tree [_] expr))
(defrecord Eval-Node-Transient [expr tree]
  EvalEvalTree
  (eval-tree [_] (eval-tree tree)))
(defrecord Eval-Node-Decompose [expr trees compose]
  EvalEvalTree
  (eval-tree [_] (compose (map eval-tree trees))))

(defrecord Step-transient [expr]
  Map-Results
  (map-result [step f] (->Step-transient (f expr)))
  BuildEvalTree
  (grow-eval-tree [_ prog orig-expr] (->Eval-Node-Transient orig-expr (grow-eval-tree (eval-step expr prog) prog expr)))
  BuildProcessTree
  (grow-process-tree [_ prog e0 id]
    (->Process-node-transient id e0 (grow-process-tree (perfect-meta-stepper prog expr) prog expr (cons 0 id)))))

(defrecord Step-variants [variants]
  Map-Results
  (map-result [step f] (->Step-variants (map (fn [[subst e]] [subst (f e)]) variants)))
  BuildProcessTree
  (grow-process-tree [_ prog e0 id]
    (->Process-node-variants
     id
     e0
     (map-indexed (fn [i [ptr e]] [ptr (grow-process-tree (perfect-meta-stepper prog e) prog e (cons i id))]) variants)))
  BuildPerfectProcessTree
  (mk-perfect [_] (->Step-variants (map (fn [[sub e]] [sub, (apply-subst e sub)]) variants))))

(defrecord Step-stop [expr]
  BuildEvalTree
  (grow-eval-tree [_ _ _] (->Eval-Leaf expr))
  BuildProcessTree
  (grow-process-tree [_ _ _ id] (->Process-leaf id expr)))

(defrecord Step-decompose [exprs compose]
  BuildEvalTree
  (grow-eval-tree [_ prog orig-expr]
    (->Eval-Node-Decompose orig-expr (map #(grow-eval-tree (eval-step %1 prog) prog %1) exprs) compose)))

;---------------------------------------------------------
; AST
;---------------------------------------------------------

(defrecord FDef [name args body]
  DefLookup
  (is-f [d n] (= n name))
  (is-g [d n] false)
  (is-g-pat [d n p-n] false))
(defrecord Pat [name vars])
(defrecord GDef [name pat args body]
  DefLookup
  (is-f [d n] false)
  (is-g [d n] (= n name))
  (is-g-pat [d n p-n] (and (= n name) (= p-n (:name pat)))))
(defrecord Program [defs])

(defrecord Var [name]
  Syntax-Operations
  (apply-subst [e s] (if (contains? s name) (get s name) e))
  (id-subst [e] {name e})
  Meta-Eval-Step
  (meta-eval-step [e p] (->Step-stop e))
  Unparse
  (unparse [e] name))

(defrecord Atom [val]
  Syntax-Operations
  (apply-subst [e s] e)
  (id-subst [e] {})
  Eval-Step
  (eval-step [e p] (->Step-stop e))
  Meta-Eval-Step
  (meta-eval-step [e p] (eval-step e p))
  Unparse
  (unparse [e] (list 'quote val)))

(defrecord Ctr [name args]
  Syntax-Operations
  (apply-subst [e s] (->Ctr name (map #(apply-subst %1 s) args)))
  (id-subst [_] (apply merge (map id-subst args)))
  Eval-Step
  (eval-step [e p]
    (if (empty? args)
      (->Step-stop e)
      (->Step-decompose args #(->Ctr name %1))))
  Meta-Eval-Step
  (meta-eval-step [e p] (eval-step e p))
  Unparse
  (unparse [e] (cons name (map unparse args))))

(defrecord FCall [name args]
  Syntax-Operations
  (apply-subst [e s] (->FCall name (map #(apply-subst %1 s) args)))
  (id-subst [_] (apply merge (map id-subst args)))
  Eval-Step
  (eval-step [e p]
    (let [{body :body params :args} (program-fdef p name)]
      (->Step-transient (apply-subst body (zipmap params args)))))
  Meta-Eval-Step
  (meta-eval-step [e p] (eval-step e p))
  Unparse
  (unparse [e] (cons name (map unparse args))))

(defn mk-vars [vn n]
  (map #(->Var (str vn '. (inc %1))) (range n)))
(defn scrutinize [g-args g-def]
  (let [[{v :name} & args] g-args
        {{ctr-name :name ctr-params :vars} :pat params :args body :body} g-def
        fresh-vars (mk-vars v (count ctr-params))
        sub (zipmap (concat ctr-params params) (concat fresh-vars args))]
    [{v (->Ctr ctr-name fresh-vars)} (apply-subst body sub)]))

(defrecord GCall [name args]
  Syntax-Operations
  (apply-subst [e s] (->GCall name (map #(apply-subst %1 s) args)))
  (id-subst [_] (apply merge (map id-subst args)))
  Eval-Step
  (eval-step [e p]
    (if
     (instance? Ctr (first args))
      (let [[{c-name :name c-args :args} & g-args] args
            {{p-vs :vars} :pat g-vs :args g-body :body} (program-gdef p name c-name)
            p (zipmap (concat p-vs g-vs) (concat c-args g-args))]
        (->Step-transient (apply-subst g-body p)))
      (let [[arg & args] args]
        (map-result (eval-step arg p) #(->GCall name (cons %1 args))))))
  Meta-Eval-Step
  (meta-eval-step [e p]
    (cond
      (instance? Ctr (first args)) (eval-step e p)
      (instance? Var (first args)) (->Step-variants (map (partial scrutinize args) (program-gdefs p name)))
      :else (let [[arg & args] args] (map-result (meta-eval-step arg p) #(->GCall name (cons %1 args))))))
  Unparse
  (unparse [e] (cons name (map unparse args))))

;---------------------------------------------------------
; Parsing and unparsing
;---------------------------------------------------------

(defn parse-expr
  "parses an expression"
  [s-expr]
  (cond
    (symbol? s-expr)
    (->Var s-expr)

    :else
    (do
      (assert (and (list? s-expr) (seq s-expr)) "unknow form")
      (if
       (and (= 'quote (first s-expr)) (symbol? (second s-expr)))
        (->Atom (second s-expr))
        (let [rator (first s-expr)
              s-rands (rest s-expr)
              args (map parse-expr s-rands)
              f-g-c (first (name rator))]
          (cond
            (= f-g-c \f) (->FCall rator args)
            (= f-g-c \g) (->GCall rator args)
            :else (->Ctr rator args)))))))

(defn parse-pat
  "parses a pattern of a g-definition"
  [s-pat]
  (->Pat (first s-pat) (rest s-pat)))

(defn parse-def
  "parses one definition of a program"
  [s-def]
  (let [[[fgname & params] _ rhs] s-def
        body (parse-expr rhs)
        fg (first (name fgname))]
    (if
     (= fg \g)
      (->GDef fgname (parse-pat (first params)) (rest params) body)
      (do (assert (= fg \f) "function name should start with `f` or 'g'")
          (->FDef fgname params body)))))

(defn parse-program
  "parses a program represented as a collection of definitions"
  [s-prog]
  (map parse-def s-prog))
