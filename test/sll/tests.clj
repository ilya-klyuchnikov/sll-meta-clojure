(ns sll.tests
  (:require [clojure.test :refer :all]
            [sll.core :refer :all]))

(deftest parse-test
  (is (= (parse-expr 'a) (->Var 'a)))
  (is (= (parse-expr ''a) (->Atom 'a)))
  (is (= (parse-expr '(f a 'b)) (->FCall 'f (list (->Var 'a) (->Atom 'b)))))
  (is (thrown? AssertionError (parse-expr '())))
  (is (thrown? AssertionError (parse-expr '{})))
  (is (thrown? AssertionError (parse-expr ':asd)))
  (is (thrown? AssertionError (parse-expr '[])))
  (is (= (parse-expr '(f-f)) (->FCall 'f-f (list)))))

(def s-prog
  '(((f-main xs ys) = (g-append xs ys))
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

(deftest parse-assert-test
  (is (thrown? AssertionError (first (parse-program '(((x xs ys) = (x xs ys))))))))

(defn map-values [f sub]
  (zipmap (keys sub) (map f (vals sub))))

(defn s-subst [s-expr s-subst]
  (let [expr (parse-expr s-expr)
        s (map-values parse-expr s-subst)]
    (unparse (apply-subst expr s))))

(deftest subst-test
  (is (= (s-subst 'a {}) 'a))
  (is (= (s-subst ''a {}) ''a))
  (is (= (s-subst '(ff x y) {}) '(ff x y)))
  (is (= (s-subst '(ff x y) '{x 'a, y 'b}) '(ff 'a 'b)))
  (is (= (s-subst '(gg x y) '{x 'a, y 'b}) '(gg 'a 'b)))
  (is (= (s-subst '(Ctr x y) '{x 'a, y 'b}) '(Ctr 'a 'b))))

(defn s-eval-tree [s-expr]
  (build-eval-tree prog (parse-expr s-expr)))

(defn s-eval [s-expr]
  (unparse (eval-tree (s-eval-tree s-expr))))

(deftest eval-test
  (is (= (s-eval '(Nil))
         '(Nil)))
  (is (= (s-eval '(Cons 'a (Nil)))
         '(Cons 'a (Nil))))
  (is (= (s-eval '(Cons 'a (Nil)))
         '(Cons 'a (Nil))))
  (is (= (s-eval '(g-append (Cons (g-eq (A) (A)) (Nil)) (Nil)))
         '(Cons (T) (Nil))))
  (is (= (s-eval '(f-id (g-append (Cons (g-eq (A) (A)) (Nil)) (Nil))))
         '(Cons (T) (Nil))))
  (is (= (s-eval '(g-append (g-append (Nil) (Nil)) (Nil)))
         '(Nil)))
  (is (= (s-eval '(g-append (Cons 'a (Cons 'b (Nil))) (Cons 'c (Cons 'd (Nil)))))
         '(Cons 'a (Cons 'b (Cons 'c (Cons 'd (Nil))))))))

(defn s-ura [s-in s-out]
  (map (fn [s] (map-values unparse s)) (ura prog (parse-expr s-in) (parse-expr s-out))))

(deftest ura-tests
  (is (= (s-ura ''a ''a)
         '({})))
  (is (= (s-ura '(f-id 'a) ''a)
         '({})))
  (is (= (s-ura '(f-id x) 'a)
         '()))
  (is (= (s-ura '(g-eq (A) (A)) '(F))
         '()))

  (is (thrown? IllegalArgumentException (s-ura '(W (A) (A)) '(F))))

  (is (= (s-ura '(g-eq (A) (A)) '(T))
         '({})))
  (is (= (s-ura '(g-eq x (A)) '(T))
         '({x (A)})))
  (is (= (s-ura '(g-eq (A) x) '(T))
         '({x (A)})))
  (is (= (s-ura '(g-eq x x) '(T))
         '({x (A)} {x (B)})))
  (is (= (s-ura '(g-eq x x) '(F))
         '()))
  (is (= (s-ura '(g-eq x y) '(T))
         '({x (A), y (A)} {x (B), y (B)})))
  (is (= (s-ura '(g-eq x y) '(F))
         '({x (A), y (B)} {x (B), y (A)})))
  (is (= (s-ura '(g-&& (g-eq x y) (g-eq x z)) '(F))
         '({x (A), y (B), z z}
           {x (B), y (A), z z}
           {x (A), y (A), z (B)}
           {x (B), y (B), z (A)})))
  (is (= (s-ura '(g-& (g-eq x y) (g-eq x z)) '(F))
         '({x (A), y (B), z (A)}
           {x (A), y (B), z (B)}
           {x (B), y (A), z (A)}
           {x (B), y (A), z (B)}
           {x (A), y (A), z (B)}
           {x (B), y (B), z (A)})))
  (is (= (s-ura '(g-eq-list (g-append x y) (Nil)) '(T))
         '({x (Nil), y (Nil)})))
  (is (= (s-ura '(g-eq-list (f-main x y) (Nil)) '(T))
         '({x (Nil), y (Nil)})))
  (is (= (s-ura '(g-eq-list (g-append x y) (Cons (A) (Nil))) '(T))
         '({x (Nil), y (Cons (A) (Nil))}
           {y (Nil), x (Cons (A) (Nil))}))))
