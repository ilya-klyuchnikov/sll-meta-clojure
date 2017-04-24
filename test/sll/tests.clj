(ns sll.tests
  (:require [clojure.test :refer :all]
            [sll.data :refer :all]
            [sll.parse :refer :all]))

(deftest prefix-test
  (is (prefix? '() '()))
  (is (prefix? '(2 1) '(3 2 1)))
  (is (not (prefix? '(3 2 1) '(2 1)))))

(deftest parse-test
  (is (= (parse-expr 'a) (->Var 'a)))
  (is (= (parse-expr ''a) (->Atom 'a)))
  (is (= (parse-expr '(f a 'b)) (->FCall 'f (list (->Var 'a) (->Atom 'b)))))
  (is (thrown? AssertionError (parse-expr '())))
  (is (= (parse-expr '(f-f)) (->FCall 'f-f (list)))))
