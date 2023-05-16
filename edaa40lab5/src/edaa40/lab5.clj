(ns edaa40.lab5)

(use 'clojure.set)
(use 'edaa40.core)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;
;; Part 1: Reading formulas in Clojure
;;



;; To make it easy for us to process formulas in Clojure, we first develop a Clojure
;; macro that allows us to write e.g.
;;
;;   (formula (-> (and a b) (not c)))
;;
;; to express the propositional formula "(a ∧ b) → ¬c".
;; The macro accepts such expressions, which may contain any of the following:
;;
;; If α and β are valid input formulae, then so are the following:
;; - T                 ("always true")
;; - F                 ("always false")
;; - propositional variables:
;;   - a
;;   - b
;;     ...
;; - (and α ... β)     (conjunction is variadic: can take arbitrarily many formulas as arguments)
;; - (or α ... β)      (disjunction is variadic: can take arbitrarily many formulas as arguments)
;; - (not α)
;; - (-> α β)          (implication)
;; - (forall [v S] α)
;; - (exists [v S] α)
;;
;; For 'forall' and 'exists', the variable 'v' can occur in α.  'S' must be a set.
;;
;; In addition, a formula may contain Clojure terms (which may also contain variables 'v').
;;
;;
;; The macro then produces output formulae that have a much more restricted form:
;; If α and β are valid output formulae, then so are the following:
;; - T                 ("always true")
;; - F                 ("always false")
;; - propositional variables:
;;   - a
;;   - b
;;     ...
;; - (L-and α β)       (conjunction always takes two parameters)
;; - (L-or α β)        (disjunction always takes two parameters)
;; - (L-not α)
;;
;; Note that we use L-and, L-or, and L-not, to avoid name clashes with the built-in Clojure names.

;; We begin with several definitions that perform part of the translation from input formulas to output formulas.

(defn expand-and
  "Combines a list of formulas that are in conjunction with each other into a single formula with the
  appropriate number of 'L-and operators"

  ([] 'T)
  ([x] x)
  ([x y] (list 'L-and x y))
  ([x y & rest] (list 'L-and x (apply expand-and (cons y rest)))))

(test? "expand-and-0" (expand-and) 'T)
(test? "expand-and-1" (expand-and 'a) 'a)
(test? "expand-and-2" (expand-and 'a 'b) '(L-and a b))
(test? "expand-and-3" (expand-and 'a 'b 'c) '(L-and a (L-and b c)))
(test? "expand-and-4" (expand-and 'a 'b 'c 'd) '(L-and a (L-and b (L-and c d))))
(test? "expand-and-5" (expand-and 'a 'b 'c 'd 'e) '(L-and a (L-and b (L-and c (L-and d e)))))


(defn expand-or
  "Combines a list of formulas that are in disjunction with each other into a single formula with the
  appropriate number of 'L-or' operators"

  ([] 'F)
  ([x] x)
  ([x y] (list 'L-or x y))  ;; Construct result list
                            ;; 'L-or tells Clojure to not evaluate the symbol "L-or" but to use it
                            ;; for itself.
  ([x y & rest] (list 'L-or x (apply expand-or (cons y rest)))))

(test? "expand-or-0" (expand-or) 'F)
(test? "expand-or-1" (expand-or 'a) 'a)
(test? "expand-or-2" (expand-or 'a 'b) '(L-or a b))
(test? "expand-or-3" (expand-or 'a 'b 'c) '(L-or a (L-or b c)))
(test? "expand-or-4" (expand-or 'a 'b 'c 'd) '(L-or a (L-or b (L-or c d))))
(test? "expand-or-5" (expand-or 'a 'b 'c 'd 'e) '(L-or a (L-or b (L-or c (L-or d e)))))

(declare expand-implication)

(defn expand-implication
;;   "Given the input formula (-> a b), generates the corresponding output formula (L-or (L-not a) b)"

  [a b]

  (list 'L-or (list 'L-not a) b)  ;; Construct result list

;;   ;; This is a one-liner.  The main challenge here is constructing the output tree without
;;   ;; Clojure attempting to evaluate that tree.  The easiest approach is to use the function `list`,
;;   ;; which constructs a list from all of its parameters.  Have a look at the line "Construct result list" in
;;   ;; `expand-or` for an example.

;;   ;; IMPLEMENT ME:
  )

;; ;; Uncomment the tests, too:
(test? "expand-implication" (expand-implication 'a 'b) '(L-or (L-not a) b))


;; Expanding the "exists" and "forall" operations is a little trickier.  We use a helper function `substitute`:

(defn substitute
  "Given a `formula`, replace all occurrences of `var` in `formula` by `value`"

  [var value formula]

  (cond
    (seq? formula)
    (map #(substitute var value %) formula) ;; recurse
    (= var formula) value
    true
    formula))

(test? "substitute-x-atom" (substitute 'x 42 'x) 42)
(test? "substitute-x-list-1" (substitute 'x 42 '(+ x 1)) '(+ 42 1))
(test? "substitute-x-list-2" (substitute 'x 42 '(+ x x)) '(+ 42 42))
(test? "substitute-x-nested-list" (substitute 'x 42 '(+ (* x 2) (+ x (- x 1) x))) '(+ (* 42 2) (+ 42 (- 42 1) 42)))
(test? "dont-substitute" (substitute 'x 42 '(+ y z 2)) '(+ y z 2))


(declare expand-forall)
(defn expand-forall
  "Given an input formula (forall [`a` `S`] `body`), substitute `a` in `body` for each of the elements of `S`.
   If `S` is the singleton `#{ s }`, returns `(substitute a s body)`.
   If `S` contains more than one element, this returns multiple `body` formulas, one per element in `S`,
     with `a` substituted suitably, and all bodies combined via  `L-and`.
   If `S` is empty, returns `T."

  [a S body]

  (if (empty? S)
    'T
    (if (= 1 (count S))
      (substitute a (first S) body)
      (apply expand-and (map #(substitute a % body) S))))

;;   ;; This was a one-liner.  I used `apply`, `for`, `substitute`, and one of the functions that we defined earlier.
;;   ;; Hint: check for a function that behaves similarly with respect to zero, one, or more arguments.

;;   ;; IMPLEMENT ME:
  )

(test? "expand-forall-0" (expand-forall 'x [] '(< x 4))        'T)
(test? "expand-forall-1" (expand-forall 'x [1] '(< x 4))     '(< 1 4))
(test? "expand-forall-2" (expand-forall 'x [1 2] '(< x 4))   '(L-and (< 1 4) (< 2 4)))
(test? "expand-forall-3" (expand-forall 'x [1 2 3] '(< x 4)) '(L-and (< 1 4) (L-and (< 2 4) (< 3 4))))


(declare expand-exists)
(defn expand-exists
  "Analogous to `expand-forall`, except that if `S` is empty, this returns `F`, and that if `S` contains
   multiple elements, the elements are connected via `L-or`."

  [a S body]

  (if (empty? S)
    'F
    (if (== 1 (count S)) (substitute a (first S) body) (apply expand-or (map #(substitute a % body) S))))



   ;; IMPLEMENT ME:
  )

 ;; Uncomment the tests, too:
(test? "expand-exists-0" (expand-exists 'x [] '(= 9 (* x x)))        'F)
(test? "expand-exists-1" (expand-exists 'x [1] '(= 9 (* x x)))     '(= 9 (* 1 1)))
(test? "expand-exists-2" (expand-exists 'x [1 2] '(= 9 (* x x)))   '(L-or (= 9 (* 1 1)) (= 9 (* 2 2))))
(test? "expand-exists-3" (expand-exists 'x [1 2 3] '(= 9 (* x x)))  '(L-or (= 9 (* 1 1)) (L-or (= 9 (* 2 2)) (= 9 (* 3 3)))))



(defn simplify-formula
  "Simplifies a formula by expanding `and`, `or`, `->`, `forall`, and `exists`."

  [phi]

  (cond
    (seq? phi) (cond
                 ;; and/or?
                 (= 'and (first phi)) (apply expand-and (map simplify-formula (rest phi)))
                 (= 'or (first phi)) (apply expand-or (map simplify-formula (rest phi)))
                 (= 'not (first phi)) (cons 'L-not (map simplify-formula (rest phi)))
                 (= '-> (first phi)) (apply expand-implication (map simplify-formula (rest phi)))
                 ;; forall / exists?
                 (contains? #{'forall 'exists} (first phi))
                 (let [quantifier (first phi)
                       vars (second phi)
                       v (first vars)
                       universe-of-v (second vars)
                       expand-fn ({'forall expand-forall 'exists expand-exists} quantifier)
                       body (third phi)
                       full-body (if (<= (count vars) 2) ; just one quantified variable?
                                   (simplify-formula body) ; directly preserve body, wrap in quote
                                   ;; more than two variables?  Let's recurse to process all pairs
                                        ;(simplify-formula `(~quantifier ~(rest (rest vars)) ~body))
                                   (simplify-formula `(~quantifier ~(rest (rest vars)) ~body)))]
                   (expand-fn v universe-of-v full-body))
                 ;; otherwise: not a quantified expression
                 true (for [alpha phi] (simplify-formula alpha))
                 ;;true (eval (for [alpha phi] (simplify-formula alpha)))
                 )

    ;; Just an atom?  Nothing to expand.
    true phi))

;; ;; Uncomment the tests:
(test? "simplify-formula-and"    (simplify-formula '(and a b c))                 '(L-and a (L-and b c)))
(test? "simplify-formula-or"     (simplify-formula '(or a b c (or)))             '(L-or a (L-or b (L-or c F))))
(test? "simplify-formula-not"    (simplify-formula '(not (or (not a))))          '(L-not (L-not a)))
(test? "simplify-formula-->"     (simplify-formula '(-> a b))                    '(L-or (L-not a) b))
(test? "simplify-formula-T-F"    (simplify-formula '(-> T F))                    '(L-or (L-not T) F))
(test? "simplify-formula-forall" (simplify-formula '(forall [x [1 2]] (or (= x 1) (= x 2))))
       '(L-and (L-or (= 1 1) (= 1 2))
               (L-or (= 2 1) (= 2 2))))
(test? "simplify-formula-exists" (simplify-formula '(exists [x [1 2]] (= x 1)))  '(L-or (= 1 1) (= 2 1)))


;; Now we define the macro "formula" to write formulas that look natural in Clojure syntax:

(defmacro formula
  "Parses a formula into a format that we can process"

  [psi]

  (simplify-formula `(quote ~psi)))

;; ;; Uncomment the tests:
(test? "formula-0"  (formula (and))                                      'T)
(test? "formula-1"  (formula (or a b (not c) d))                         '(L-or a (L-or b (L-or (L-not c) d))))
(test? "formula-2"  (formula (forall [x [1 2 3]] (-> (< x 2) (= x 1))))
       '(L-and (L-or (L-not (< 1 2)) (= 1 1))
               (L-and (L-or (L-not (< 2 2)) (= 2 1))
                      (L-or (L-not (< 3 2)) (= 3 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Part 2: Evaluating Formulas
;;

;; We will soon implement an evaluation mechanism for logical formulas that supports different Boolean algebras.
;;
;; Before we do that, we first package up the propositional boolean logic that we discussed in class.
;; Here, we call that logic "binary logic", to make it more explicit that we only distinguish between
;; zeroes and ones:

(def binary-T 1)

(def binary-F 0)

(defn binary-not
  "Binary logic `not` function. Takes `1` and returns `0`, or vice versa."

  [n]

  ;; Implementation via map lookup:
  ({1 0,
    0 1} n))

(test? "binary-not(0)" (binary-not 0) 1)
(test? "binary-not(1)" (binary-not 1) 0)

(declare binary-and)
(defn binary-and
  "Binary logic `and` function.  Returns `1` if `l` = `r` = `1`, otherwise `0`."

  [l r]

  ;;(if (and (== l 1) (== r 1)) 1 0)

  ({[1 1] 1,
    [1 0] 0,
    [0 1] 0,
    [0 0] 0} [l r])
   ;; IMPLEMENT ME:
  )

 ;; Uncomment the tests, too:
(test? "binary-and(0 0)" (binary-and 0 0) 0)
(test? "binary-and(0 1)" (binary-and 0 1) 0)
(test? "binary-and(1 0)" (binary-and 1 0) 0)
(test? "binary-and(1 1)" (binary-and 1 1) 1)


(declare binary-or)
(defn binary-or
  "Binary logic `or` function.  Returns `0` if `l` = `r` = `0`, otherwise `1`."

  [l r]

  ;;(if (or (== l 1) (== r 1)) 1 0)

  ({[1 0] 1,
    [0 1] 1,
    [1 1] 1,
    [0 0] 0} [l r])

   ;; IMPLEMENT ME:
  )

 ;; Uncomment the tests, too:
(test? "binary-or(0 0)" (binary-or 0 0) 0)
(test? "binary-or(0 1)" (binary-or 0 1) 1)
(test? "binary-or(1 0)" (binary-or 1 0) 1)
(test? "binary-or(1 1)" (binary-or 1 1) 1)


;; We package boolean algebra logic operations together into one map datastructure:

(def binary-boolean-algebra
  "Boolean algebra for binary logic"

  {:T 1,
   :F 0,
   :and binary-and,
   :or  binary-or,
   :not binary-not})

(defn eval-formula
  "Evaluates `formula` under the given `boolean-algebra`, with a valuation mapping (map) from `valuation` for propositions."

  [boolean-algebra valuation formula]

  (cond
    (seq? formula) (let [op (first formula)
                         args (map #(eval-formula boolean-algebra valuation %) (rest formula))]
                     (cond
             ;true (list :op op :L-and (boolean-algebra :L-and) :args args)
                       (= 'L-and op) (apply (boolean-algebra :and) args)
                       (= 'L-or op)  (apply (boolean-algebra :or) args)
                       (= 'L-not op) (apply (boolean-algebra :not) args)
             ;; otherwise we have normal Clojure operation
                       true (if (eval (cons op (rest formula)))
               ;; interpret result as "T" or "F"
                              (boolean-algebra :T)
                              (boolean-algebra :F))))
    (= 'T formula) (boolean-algebra :T)
    (= 'F formula) (boolean-algebra :F)
    ;true (list valuation formula :gives (valuation formula))  ;; proposition?  Look up in valuation function
    true (valuation formula)  ;; proposition?  Look up in valuation function
    ))

;; ;; Uncomment the tests:
(test? "eval-formula-binary(T)"           (eval-formula binary-boolean-algebra {} (formula T)) 1)
(test? "eval-formula-binary(or T F)"      (eval-formula binary-boolean-algebra {} (formula (or T F))) 1)
(test? "eval-formula-binary(and T F)"     (eval-formula binary-boolean-algebra {} (formula (and T F))) 0)
(test? "eval-formula-binary(forall)"      (eval-formula binary-boolean-algebra {} (formula (forall [x [1 2 3 4 5]] (-> (> x 2) (or (= 9 (* x x)) (contains? #{4 5} x)))))) 1)
(test? "eval-formula-binary(and T not F)" (eval-formula binary-boolean-algebra {} (formula (and T (not F)))) 1)

 ;; We need to quote variable names in the `valuation-map` to define them:

(test? "eval-formula-binary(a:0)" (eval-formula binary-boolean-algebra {'a 0} (formula a)) 0)
(test? "eval-formula-binary(a:1)" (eval-formula binary-boolean-algebra {'a 1} (formula a)) 1)
(test? "eval-formula-binary(a <-> b: 0,0)" (eval-formula binary-boolean-algebra {'a 0, 'b 0} (formula (or (and a b) (and (not a) (not b))))) 1)
(test? "eval-formula-binary(a <-> b: 1,0)" (eval-formula binary-boolean-algebra {'a 0, 'b 1} (formula (or (and a b) (and (not a) (not b))))) 0)
(test? "eval-formula-binary(a <-> b: 0,1)" (eval-formula binary-boolean-algebra {'a 1, 'b 0} (formula (or (and a b) (and (not a) (not b))))) 0)
(test? "eval-formula-binary(a <-> b: 1,1)" (eval-formula binary-boolean-algebra {'a 1, 'b 1} (formula (or (and a b) (and (not a) (not b))))) 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Part 3: Truth Tables
;;

(declare binary-truth-table-with-valuations)
(defn binary-truth-table-with-valuations
  "Recursively constructs a truth table by trying all combinations of all `propositions` set to `1` and `0`.  `valuations` carries the intermediate result of binding propositions to values `1` and `0`.
   See `binary-truth-table` (below) for a description of the output format."

  [propositions valuations formula]

  ; [a], {}, T
  ; Is it empty? No, then continue
  ; Does it only have one propositions?
  ;    -> If yes, we evaluate the proposition p using the formula when {p 0} and {p 1}, and append these evaluations into a result list.
  ;    -> If no, then we go through each proposition recursively 


  (if (and (empty? propositions) (empty? valuations))
    (list (list (eval-formula binary-boolean-algebra valuations formula)))
    (if (empty? propositions)
      (list (eval-formula binary-boolean-algebra valuations formula))
      (let [result
            (for [value [0 1]]
              (let [sub-result (binary-truth-table-with-valuations
                                (rest propositions)
                                (assoc valuations (first propositions) value)
                                formula)]
                (cons value sub-result)))]
        result)))


   ;; (for [a A b B] [a b])

   ;; This was about ten lines for me.  The function is recursive, and each recursion step should
   ;; remove `(first propositions)` and then pass `(rest propositions)` to the next recursion step.  Thus,
   ;; the length of the list of `propositions` decreases, and the function is well-defined.
   ;; I used functions like `empty?`, `list`, and `cons` (which prepends an element to a list), as well as `for`.
   ;;
   ;; The function `assoc` plays a key role here for extending the `valuations` map on recursion.  As with all the other
   ;; functions that we use, `assoc` does not modify any existing maps, so you don't have to worry about side effects.
   ;;
   ;; See `binary-truth-table` for more information on the output format.

   ;; How many output lists do you need to produce for 1, 2, 3, 4, ... propositions?

  ;;(if (empty? propositions)
  ;;  (list valuations)
  ;;  (for [v propositions] (binary-truth-table-with-valuations (rest propositions) (assoc valuations (first propositions) propositions) formula))) 
  )

(defn binary-truth-table
  "Constructs a truth table by trying all combinations of all `propositions` set to `1` and `0` in the input formula.
  The output is a list of lists of `0` and `1` values.  For example, if `propositions` is `['a 'b 'c]`, then
  the output will consist of the list
  `((0 0 0 X0)
    (0 0 1 X1)
    (0 1 0 X2)
    (0 1 1 X3)
    (1 0 0 X4)
    (1 0 1 X5)
    (1 1 0 X6)
    (1 1 1 X7))`

  where:
  - `X0` is the result of evaluating `formula` with the valuation map `{'a 0, 'b 0, 'c 0}` in `binary-logic`,
  - `X1` is the result of evaluating `formula` with the valuation map `{'a 0, 'b 0, 'c 1}` in `binary-logic`,
  - `X2` is the result of evaluating `formula` with the valuation map `{'a 0, 'b 1, 'c 0}` in `binary-logic`
  and so on."

  [propositions formula]

  (binary-truth-table-with-valuations propositions {} formula))

;; ;; Uncomment the tests:
(binary-truth-table ['a, 'b] (formula (or a (not b))))
(test? "truthtable-trivial" (binary-truth-table [] (formula T)) '((1)))
(test? "truthtable-vacuous" (binary-truth-table ['a] (formula T)) '((0 1) (1 1)))
(test? "truthtable-a" (binary-truth-table ['a] (formula a)) '((0 0) (1 1)))
(test? "truthtable-not-a" (binary-truth-table ['a] (formula (not a))) '((0 1)
                                                                        (1 0)))
(test? "truthtable-<-" (binary-truth-table ['a, 'b] (formula (or a (not b)))) '((0 0  1)
                                                                                (0 1  0)
                                                                                (1 0  1)
                                                                                (1 1  1)))
(test? "truthtable-3-vars" (binary-truth-table ['a, 'b, 'c] (formula (or (and a c) (not b) (and (not c) b))))
       '((0 0 0  1)
         (0 0 1  1)
         (0 1 0  1)
         (0 1 1  0)
         (1 0 0  1)
         (1 0 1  1)
         (1 1 0  1)
         (1 1 1  1)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Part 4: Many-Worlds Logic
;;


;; We implement "Many-Worlds Logic" with five worlds (to keep the implementation simple).

(def many-worlds #{'A 'B 'C 'D 'E})

(defn many-worlds-not
  [S]
  (difference many-worlds S))

(declare many-worlds-logic)
(def many-worlds-logic
  ;; Constants and operations for Many-Worlds Logic for our five `many-worlds`.
  ;; Hint: my solution involves no additional function definitions; I merely re-used existing functions.

  ;; IMPLEMENT ME:


  {:T  1,
   :F  0,
   :and intersection,
   :or  union,
   :not many-worlds-not})

;; ;; Uncomment the tests:
(test? "many-worlds-a"
       (eval-formula many-worlds-logic {'a #{'A 'E}
                                        'b #{'B 'E}
                                        'c #{'C 'E}}
                     (formula a))
       #{'A 'E})

(test? "many-worlds-not-a"
       (eval-formula many-worlds-logic {'a #{'A 'E}
                                        'b #{'B 'E}
                                        'c #{'C 'E}}
                     (formula (not a)))
       #{'B 'C 'D})

(test? "many-worlds-a&c"
       (eval-formula many-worlds-logic {'a #{'A 'E}
                                        'b #{'B 'E}
                                        'c #{'C 'E}}
                     (formula (and a c)))
       #{'E})

(test? "many-worlds-implication-1"
       (eval-formula many-worlds-logic {'a #{'A 'E}
                                        'b #{'B 'E}
                                        'c #{'C 'E}}
                     (formula (-> a b)))
       #{'B 'C 'D 'E})


(test? "many-worlds-implication-2"
       (eval-formula many-worlds-logic {'a #{'A 'E}
                                        'b #{'B 'E}
                                        'c #{'C 'E}
                                        'd #{'C 'D 'E}}
                     (formula (-> (or a d) (and b c))))
       #{'B 'E})
