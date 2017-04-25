(ns sll.tests
  (:require [clojure.test :refer :all]
            [sll.core :refer :all]
            [clojure.pprint :refer [pprint]]))

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

(deftest vnames-test
  (is (= (vnames (parse-expr 'a)) '(a)))
  (is (= (vnames (parse-expr ''a)) '()))
  (is (= (vnames (parse-expr '(Ctr a b c))) '(a b c)))
  (is (= (vnames (parse-expr '(Ctr a b (Ctr a b)))) '(a b a b))))

(def s-prog
  '(
     ((f-main xs ys) = (g-append xs ys))
     ((g-flatten (Leaf x)) = (Cons x (Nil)))
     ((g-flatten (Node lt x rt)) = (g-append (g-flatten lt) (Cons x (g-flatten rt))))
     ; list concatenation
     ((g-append (Nil) ys) = ys)
     ((g-append (Cons x xs) ys) = (Cons x (g-append xs ys)))
     ; equality over char (A|B)
     ((g-eq (A) s) = (g-eq-A s))
     ((g-eq (B) s) = (g-eq-B s))
     ((g-eq-A (A)) = (T))
     ((g-eq-A (B)) = (F))
     ((g-eq-B (A)) = (F))
     ((g-eq-B (B)) = (T))
     ; equality over 2 lists
     ((g-eq-list (Nil) l2) = (g-eq-list-nil l2))
     ((g-eq-list (Cons x xs) l2) = (g-eq-list-cons l2 x xs))
     ((g-eq-list-cons (Nil) x xs) = (F))
     ((g-eq-list-cons (Cons y ys) x xs) = (g-&& (g-eq x y) (g-eq-list xs ys)))
     ((g-eq-list-nil (Nil)) = (T))
     ((g-eq-list-nil (Cons x xs)) = (F))
     ; boolean and (short-circuit and)
     ((g-&& (F) b) = (F))
     ((g-&& (T) b) = b)
     ; total &
     ((g-& (F) b) = (g-b b (F)))
     ((g-& (T) b) = (g-b b b))
     ; dummy function - just to enforce pattern matching
     ((g-b (F) x) = x)
     ((g-b (T) x) = x)
     ; idle function for tests
     ((g-zero (Zero) x) = x)
     ((g-zero (Succ n) x) = (g-zero n (F)))
     ((f-id x) = x)))


(def prog
  (parse-program s-prog))

(defn s-renaming [s-exp1 s-exp2]
  (renaming (parse-expr s-exp1) (parse-expr s-exp2)))

(deftest renaming-test
  (is (= (s-renaming 'a 'b) {'a 'b}))
  (is (= (s-renaming ''a 'b) false))
  (is (= (s-renaming '(P x y) '(P y x)) {'x 'y, 'y 'x}))
  (is (= (s-renaming '(P x y) '(P x x)) false))
  (is (= (s-renaming '(P x x) '(P x y)) false)))

(defn s-eval-tree [s-expr]
  (build-eval-tree prog (parse-expr s-expr)))

(defn s-eval [s-expr]
  (unparse (eval-tree (s-eval-tree s-expr))))

(deftest eval-test
  (is (= (s-eval '(Nil))
         '(Nil)))
  (is (= (s-eval '(Cons 'a (Nil)))
         '(Cons 'a (Nil))))
  (is (= (s-eval '(g-append (Cons (g-eq (A) (A)) (Nil)) (Nil)) )
         '(Cons (T) (Nil))))
  (is (= (s-eval '(f-id (g-append (Cons (g-eq (A) (A)) (Nil)) (Nil))))
         '(Cons (T) (Nil))))
  (is (= (s-eval '(g-append (g-append (Nil) (Nil)) (Nil)))
         '(Nil)))
  (is (= (s-eval '(g-append (Cons 'a (Cons 'b (Nil))) (Cons 'c (Cons 'd (Nil)))))
         '(Cons 'a (Cons 'b (Cons 'c (Cons 'd (Nil))))))))

(defn s-meta-step [s-expr] ((meta-stepper prog) (parse-expr s-expr)))
(defn s-perfect-meta-step [s-expr] ((perfect-meta-stepper prog) (parse-expr s-expr)))

(pprint (s-meta-step '(Nil)))
(pprint (s-meta-step '(g-append x y)))
(pprint (s-meta-step '(g-append x x)))
(pprint (s-perfect-meta-step '(g-append x x)))

(defn s-build-process-tree [s-expr]
  (build-process-tree prog (parse-expr s-expr)))

(pprint (s-build-process-tree '(Nil)))
(pprint (s-build-process-tree '(Cons a b)))
(pprint (s-build-process-tree '(g-append (Nil) b)))
(pprint (s-build-process-tree '(g-eq x y)))