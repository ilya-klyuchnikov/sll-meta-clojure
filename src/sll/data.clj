(ns sll.data
  (:gen-class)
  (:require [clojure.set :refer [map-invert]]))

; terms
(defprotocol Stub
  (stub [exp])
  (vnames [exp]))

; terms
(defrecord Var [name]
  Stub
  (stub [e]
    (->Var '_))
  (vnames [e]
    (list name)))

(defrecord Atom [val]
  Stub
  (stub [e]
    e)
  (vnames [e]
    (list)))

(defrecord Ctr [name args]
  Stub
  (stub [e]
    (->Ctr name (map stub args)))
  (vnames [e]
    (apply concat (map vnames args))))

(defrecord FCall [name args]
  Stub
  (stub [e]
    (->FCall name (map stub args)))
  (vnames [e]
    (apply concat (map vnames args))))

(defrecord GCall [name args]
  Stub
  (stub [e]
    (->GCall name (map stub args)))
  (vnames [e]
    (apply concat (map vnames args))))


(defrecord Pat [name vars])
(defrecord FDef [name args body])
(defrecord GDef [name pat args body])
(defrecord Program [defs])

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
