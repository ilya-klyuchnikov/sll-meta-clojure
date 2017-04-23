(ns sll.parse-test
  (:require [clojure.test :refer :all]
            [sll.data :refer :all]
            [sll.parse :refer :all]))

(deftest parse-test
  (is (= (parse-expr 'a) (->Var 'a)))
  (is (= (parse-expr ''a) (->Atom 'a)))
  (is (= (parse-expr '(f a 'b)) (->FCall 'f (list (->Var 'a) (->Atom 'b))))))
