(ns sll.data
  (:gen-class)
  (:require [clojure.set :refer [map-invert]]))

; terms
(defprotocol Syntax-Operations
  (subst [exp s])
  (stub [exp])
  (vnames [exp]))

; terms
(defrecord Var [name]
  Syntax-Operations
  (subst [e s] (if (contains? s name) (get s name) e))
  (stub [e] (->Var '_))
  (vnames [e] (list name)))

(defrecord Atom [val]
  Syntax-Operations
  (subst [e s] e)
  (stub [e] e)
  (vnames [e] (list)))

(defrecord Ctr [name args]
  Syntax-Operations
  (subst [e s] (->Ctr name (map subst args)))
  (stub [e] (->Ctr name (map stub args)))
  (vnames [e] (apply concat (map vnames args))))

(defrecord FCall [name args]
  Syntax-Operations
  (subst [e s] (->FCall name (map subst args)))
  (stub [e] (->FCall name (map stub args)))
  (vnames [e] (apply concat (map vnames args))))

(defrecord GCall [name args]
  Syntax-Operations
  (subst [e s] (->GCall name (map subst args)))
  (stub [e] (->GCall name (map stub args)))
  (vnames [e] (apply concat (map vnames args))))

(defprotocol DefLookup
  "lookup of definitions in a program"
  (is-f [d n])
  (is-g [d n])
  (is-g-pat [d n p-n]))

(defrecord Pat [name vars])

(defrecord FDef [name args body]
  DefLookup
  (is-f [d n] (= (n name)))
  (is-g [d n] false)
  (is-g-pat [d n p-n] false))

(defrecord GDef [name pat args body]
  DefLookup
  (is-f [d n] false)
  (is-g [d n] (= (n name)))
  (is-g-pat [d n p-n] (and (= n name) (= p-n (:name pat)))))

(defrecord Program [defs])

; unfold of f-function
(defrecord Unfold [])
; constructor match
(defrecord Ctr-match [cname])

(defprotocol Map-Results
  (map-result [step f]))

; step
(defrecord Step-transient [info expr]
  Map-Results
  (map-result [step f] (->Step-transient info (f expr))))

(defrecord Step-stop [expr])
(defrecord Step-decompose [name exprs])
(defrecord Step-variants [variants]
  Map-Results
  (map-result [step f] (->Step-variants (map (fn [v] (list (first v) (f (second v))))))))

(defrecord Edge-transient [info tree])
(defrecord Edge-decompose [name trees])
(defrecord Edge-variants [variants])

(defrecord Node [expr edge])
(defrecord Leaf [expr])

(defn mk-subst [names vals]
  (zipmap names vals))
(def empty-subst {})

; ///
(defn remap [sub1 sub2]
  (zipmap (keys sub1) (map (fn [k] (subst k sub2)) (vals sub1))))


(defn map-values [f sub]
  (zipmap (keys sub) (map f (vals sub))))


(defn program-fdef [program f-name]
  (first (filter (fn [d] (is-f d f-name)) program)))

(defn program-gdefs [program g-name]
  (filter (fn [d] (is-g d g-name)) program))

(defn program-gdef [program g-name ctr-name]
  (filter (fn [d] (is-g-pat d g-name ctr-name)) program))

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
