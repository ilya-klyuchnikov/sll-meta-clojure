(ns sll.parse
  (:gen-class)
  (:require [sll.data :refer :all]))

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
