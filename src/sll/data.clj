(ns sll.data
  (:gen-class))

; terms
(defrecord Var [name])
(defrecord Atom [val])
(defrecord Ctr [name args])
(defrecord FCall [name args])
(defrecord GCall [name args])

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