(ns sll.parse
  (:gen-class)
  (:require [sll.data :refer :all]))

(defn unknown-form []
  (throw (Exception. "unknown form")))

(defn parse-expr [s-expr]
  (cond
    (symbol? s-expr) (->Var s-expr)
    (seq? s-expr)
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
          :else (->Ctr rator args))))
    :else (unknown-form)))
