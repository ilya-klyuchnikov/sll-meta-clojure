(ns sll.data-test
  (:require [clojure.test :refer :all]
            [sll.data :refer :all]))

(deftest prefix-test
  (is (prefix? '() '()))
  (is (prefix? '(2 1) '(3 2 1)))
  (is (not (prefix? '(3 2 1) '(2 1)))))

