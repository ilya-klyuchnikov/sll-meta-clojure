(ns sll.data
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
  (map-result [step f] (->Step-variants (map (fn [v] (list (first v) (f (second v))))))))
(defrecord Step-stop [expr])
(defrecord Step-decompose [name exprs])

;--------------------------------------------------------------------------------------------

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
  Unparse
  (unparse [e] name))

(defrecord Atom [val]
  Syntax-Operations
  (subst [e s] e)
  (stub [e] e)
  (vnames [e] (list))
  Eval-Step
  (step [e p] (->Step-stop e))
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
  Unparse
  (unparse [e] (cons name (map unparse args))))

;--------------------------------------------------------------------------------------------

(defn eval-stepper [prog] (fn [e] (step e prog)))

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
  (map (fn [i] (str vn '. (+1 i))) (range n)))

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
