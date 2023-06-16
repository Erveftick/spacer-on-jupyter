(declare-rel inv2 (Int Int Int Int))
(declare-rel fail ())
(declare-var X Int)
(declare-var Y Int)
(declare-var C Int)
(declare-var D Int)
(declare-var E Int)
(declare-var F Int)
(rule (=> (and 
                ;;(<= D 5000)
                (= D 5000)
                (= C 10000)
                (= X 0)
                (= Y D)) 
        (inv2 X Y D C)))
(rule (let ((a!1 (and (inv2 X Y D C)
                 (= E (+ X 1))
                 (= F (ite (>= X D) (+ Y 1) Y)))))
  (=> a!1 (inv2 E F D C))))
(rule (=> (and (inv2 X Y D C) 
               (= X C)
               (not (= Y X))) fail))
(query fail)