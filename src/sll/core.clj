(ns sll.core
  (:gen-class)
  (:require [clojure.set :refer [map-invert]]))

; terms
(defprotocol Syntax-Operations
  (subst [exp s])
  (stub [exp])
  (vnames [exp]))

(defprotocol Map-Results
  (map-result [step f]))

(defprotocol Eval-Step
  (step [expr prog]))

(defprotocol Meta-Eval-Step
  (meta-step [expr prog]))

(defprotocol DefLookup
  "lookup of definitions in a program"
  (is-f [d n])
  (is-g [d n])
  (is-g-pat [d n p-n]))

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


(defn program-fdef [program f-name]
  (first (filter (fn [d] (is-f d f-name)) program)))

(defn program-gdefs [program g-name]
  (seq (filter (fn [d] (is-g d g-name)) program)))

(defn program-gdef [program g-name ctr-name]
  (first (filter (fn [d] (is-g-pat d g-name ctr-name)) program)))

(defrecord Unfold [])
(defrecord Ctr-match [cname])

;--------------------------------------------------------------------------------------------

(defrecord Edge-transient [info tree])
(defrecord Edge-decompose [name trees])
(defrecord Edge-variants [variants])

(defrecord Node [expr edge])
(defrecord Leaf [expr])

; step = (stepper expr)
(defrecord Step-transient [info expr]
  Map-Results
  (map-result [step f] (->Step-transient info (f expr))))

(defrecord Step-variants [variants]
  Map-Results
  (map-result [step f] (->Step-variants (map (fn [v] [(first v) (f (second v))]) variants))))
(defrecord Step-stop [expr])
(defrecord Step-decompose [name exprs])

;--------------------------------------------------------------------------------------------

(def scrutinize)
(def mk-vars)

(defprotocol Unparse
  (unparse [e]))

(extend-protocol Unparse
  nil
  (unparse [_] nil))

(defrecord Var [name]
  Syntax-Operations
  (subst [e s] (if (contains? s name) (get s name) e))
  (stub [e] (->Var '_))
  (vnames [e] (list name))
  Meta-Eval-Step
  (meta-step [e p] (->Step-stop e))
  Unparse
  (unparse [e] name))

(defrecord Atom [val]
  Syntax-Operations
  (subst [e s] e)
  (stub [e] e)
  (vnames [e] (list))
  Eval-Step
  (step [e p] (->Step-stop e))
  Meta-Eval-Step
  (meta-step [e p] (step e p))
  Unparse
  (unparse [e] (list 'quote val)))

(defrecord Ctr [name args]
  Syntax-Operations
  (subst [e s] (->Ctr name (map (fn [e] (subst e s)) args)))
  (stub [e] (->Ctr name (map stub args)))
  (vnames [e] (apply concat (map vnames args)))
  Eval-Step
  (step [e p]
    (do
    (if (empty? args)
      (->Step-stop e)
      (->Step-decompose name args))))
  Meta-Eval-Step
  (meta-step [e p] (step e p))
  Unparse
  (unparse [e] (cons name (map unparse args))))

(defrecord FCall [name args]
  Syntax-Operations
  (subst [e s] (->FCall name (map (fn [e] (subst e s)) args)))
  (stub [e] (->FCall name (map stub args)))
  (vnames [e] (apply concat (map vnames args)))
  Eval-Step
  (step [e p]
    (let [f (program-fdef p name)]
      (->Step-transient (->Unfold) (subst (:body f) (zipmap (:args f) args)))))
  Meta-Eval-Step
  (meta-step [e p] (step e p))
  Unparse
  (unparse [e] (cons name (map unparse args))))

(defrecord GCall [name args]
  Syntax-Operations
  (subst [e s] (->GCall name (map (fn [e] (subst e s)) args)))
  (stub [e] (->GCall name (map stub args)))
  (vnames [e] (apply concat (map vnames args)))
  Eval-Step
  (step [e p]
    (if
      (instance? Ctr (first args))
      ; TODO: destructuring
      (let [c (first args)
            c-name (:name c)
            g-args (rest args)
            c-args (:args c)
            g-def (program-gdef p name c-name)
            g-pat (:pat g-def)
            g-vs (:args g-def)
            p-vs (:vars g-pat)
            g-body (:body g-def)
            s (zipmap (concat p-vs g-vs) (concat c-args g-args))]
        (->Step-transient (->Ctr-match c-name) (subst g-body s)))
      (let [arg (first args)
            args (rest args)
            inner-step (step arg p)]
        (map-result inner-step (fn [e] (->GCall name (cons e args)))))))
  Meta-Eval-Step
  (meta-step [e p]
    (cond
      (instance? Ctr (first args)) (step e p)
      (instance? Var (first args))
      (->Step-variants (map (partial scrutinize args) (program-gdefs p name)))
      :else (let [arg (first args)
                  args (rest args)
                  inner-step (meta-step arg p)]
              (map-result inner-step (fn [e] (->GCall name (cons e args)))))))
  Unparse
  (unparse [e] (cons name (map unparse args))))

(defn scrutinize [g-args g-def]
  (let [v (:name (first g-args))
       args (rest g-args)
       pat (:pat g-def)
       params (:args g-def)
       body (:body g-def)
       ctr-name (:name pat)
       ctr-params (:vars pat)
       fresh-vars (mk-vars v (count ctr-params))
       sub (zipmap (concat ctr-params params) (concat fresh-vars args))]
    [{v (->Ctr ctr-name fresh-vars)} (subst body sub)]))

;--------------------------------------------------------------------------------------------
; PARSING
;--------------------------------------------------------------------------------------------

(defn parse-expr
  "parses an expression"
  [s-expr]
  (cond
    (symbol? s-expr) (->Var s-expr)
    (seq? s-expr)
    (do
      (assert (not (empty? s-expr)) "unknow form")
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
            :else (->Ctr rator args)))))
    :else (assert false "unknown form")))

(defn parse-pat
  "parses a pattern of a g-definition"
  [s-pat]
  (->Pat (first s-pat) (rest s-pat)))

(defn parse-def
  "parses one definition of a program"
  [s-def]
  (let [lhs (nth s-def 0)
        rhs (nth s-def 2)
        body (parse-expr rhs)
        fgname (first lhs)
        params (rest lhs)
        fg (first (name fgname))]
    (cond
      (= fg \f) (->FDef fgname params body)
      (= fg \g) (->GDef fgname (parse-pat (first params)) (rest params) body))))

(defn parse-program
  "parses a program represented as a collection of definitions"
  [s-prog]
  (map parse-def s-prog))


;--------------------------------------------------------------------------------------------

(defn eval-stepper [prog] (fn [e] (step e prog)))
(defn meta-stepper [prog] (fn [e] (meta-step e prog)))

(defn perfect-meta-stepper [prog]
  (let [stepper (meta-stepper prog)]
    (letfn [(perfect-step [e]
              (let [inner-step (stepper e)]
                (if (instance? Step-variants inner-step)
                  (->Step-variants (map (fn [vr] (let [[sub e] vr] [sub, (subst e sub)])) (:variants inner-step)))
                  inner-step)))]
      perfect-step)))

(defn build-eval-tree [prog expr]
  (let [stepper (eval-stepper prog)]
    (letfn [(build [e]
              (let [step (stepper e)]
                (cond
                  (instance? Step-stop step) (->Leaf (:expr step))
                  (instance? Step-transient step) (->Node e (->Edge-transient (:info step) (build (:expr step))))
                  (instance? Step-decompose step) (->Node e (->Edge-decompose (:name step) (map build (:exprs step)))))))]
      (build expr))))

(defn eval-tree [tree]
  (cond
    (instance? Leaf tree) (:expr tree)
    (instance? Node tree) (let [edge (:edge tree)]
                            (cond
                              (instance? Edge-transient edge) (eval-tree (:tree edge))
                              (instance? Edge-decompose edge) (->Ctr (:name edge) (map eval-tree (:trees edge)))))))

;--------------------------------------------------------------------------------------------

(defn mk-subst [names vals]
  (zipmap names vals))
(def empty-subst {})

; ///
(defn remap [sub1 sub2]
  (zipmap (keys sub1) (map (fn [k] (subst k sub2)) (vals sub1))))


(defn map-values [f sub]
  (zipmap (keys sub) (map f (vals sub))))

(defn mk-vars [vn n]
  (map (fn [i] (->Var (str vn '. (+ 1 i)))) (range n)))

(defn id-subst [e]
  (into {} (map (fn [n] [n (->Var n)]) (vnames e))))

; syntax utilities
(defn prefix? [path1 path2]
  (cond
    (> (count path1) (count path2)) false
    (= (count path1) (count path2)) (= path1 path2)
    :else (prefix? path1 (rest path2))))

(defn renaming [e1 e2]
  (and
    (= (stub e1) (stub e2))
    (let [vns1 (vnames e1)
          vns2 (vnames e2)
          ren1 (zipmap vns1 vns2)
          ren2 (zipmap vns2 vns1)]
      (and (= ren1 (map-invert ren2)) (= ren2 (map-invert ren1)) ren1))))

;--------------------------------------------------------------------------------------------
; process tree
;--------------------------------------------------------------------------------------------

(defrecord Process-edge-transient [info tree])
(defrecord Process-edge-decompose [name trees])
(defrecord Process-edge-variants [variants])

(defrecord Process-node [id expr edge])
(defrecord Process-leaf [id expr])

(defn build-process-tree [prog expr]
  (let [stepper (perfect-meta-stepper prog)]
    (letfn [(build [expr id]
              (let [step (stepper expr)]
                (cond

                  (instance? Step-stop step)
                  (->Process-leaf id (:expr step))

                  (instance? Step-transient step)
                  (->Process-node id expr (->Process-edge-transient (:info step) (build (:expr step) (cons 0 id))))

                  (instance? Step-variants step)
                  (->Process-node id expr (->Process-edge-variants
                                            (map-indexed (fn [i [x y]] [x (build y (cons i id))]) (:variants step))))

                  (instance? Step-decompose step)
                  (->Process-node id expr (->Process-edge-decompose
                                            (:name step)
                                            (map-indexed (fn [i e] (build e (cons i id))) (:exprs step)))))))]
      (build expr '()))))

;--------------------------------------------------------------------------------------------
; URA
;--------------------------------------------------------------------------------------------

(defn ura [prog in out]
  (let [tree (build-process-tree prog in)]
    (letfn [(traverse [queue]
              (if (empty? queue)
                '()
                (let [p (first queue)
                      queue (rest queue)
                      subst (first p)
                      tree (second p)]
                  (cond
                    (and (instance? Process-leaf tree) (= out (:expr tree)))
                    (cons subst (traverse queue))

                    (instance? Process-leaf tree)
                    (traverse queue)

                    (instance? Process-node tree)
                    (let [edge (:edge tree)]
                      (cond
                        (instance? Process-edge-transient edge)
                        (traverse (concat queue (list [subst (:tree edge)])))

                        (instance? Process-edge-variants edge)
                        (let [delta (map (fn [[s t]] [(remap subst s) t]) (:variants edge))]
                          (traverse (concat queue delta)))))))))]

      (traverse (list [(id-subst in) tree])))))