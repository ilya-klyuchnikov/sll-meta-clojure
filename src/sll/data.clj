(ns sll.data
  (:gen-class))

(defprotocol Stub
  (stub [exp]))

; terms
(defrecord Var [name]
  Stub
  (stub [e]
    (->Var '_)))

(defrecord Atom [val]
  Stub
  (stub [e]
    e))

(defrecord Ctr [name args]
  Stub
  (stub [e]
    (->Ctr name (map stub args))))

(defrecord FCall [name args]
  Stub
  (stub [e]
    (->FCall name (map stub args))))

(defrecord GCall [name args]
  Stub
  (stub [e]
    (->GCall name (map stub args))))


(defn prefix? [path1 path2]
  (cond
    (> (count path1) (count path2)) false
    (= (count path1) (count path2)) (= path1 path2)
    :else (prefix? path1 (rest path2))))