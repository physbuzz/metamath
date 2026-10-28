
#lang sicp

;; =====================================================
;; ======================Streams=========================
;; =====================================================
(define (stream-car stream) (car stream))
(define (stream-cdr stream) (force (cdr stream)))
(define (singleton-stream x)
        (cons-stream x the-empty-stream))
(define (stream-map proc s)
  (if (stream-null? s)
      the-empty-stream
      (cons-stream (proc (stream-car s))
                   (stream-map proc (stream-cdr s)))))
(define (stream-ref s n) 
        (if (<= n 0)
            (stream-car s)
            (stream-ref (stream-cdr s) (- n 1))))
(define (stream-append s1 s2)
  (if (stream-null? s1)
      s2
      (cons-stream (stream-car s1)
                   (stream-append (stream-cdr s1) s2))))
(define (stream-append-delayed s1 delayed-s2)
  (if (stream-null? s1)
      (force delayed-s2)
      (cons-stream
       (stream-car s1)
       (stream-append-delayed (stream-cdr s1) delayed-s2))))
(define (interleave-delayed s1 delayed-s2)
  (if (stream-null? s1)
      (force delayed-s2)
      (cons-stream
       (stream-car s1)
       (interleave-delayed (force delayed-s2)
                           (delay (stream-cdr s1))))))
(define (stream-flatmap proc s)
  (flatten-stream (stream-map proc s)))
(define (flatten-stream stream)
  (if (stream-null? stream)
      the-empty-stream
      (interleave-delayed
       (stream-car stream)
       (delay (flatten-stream (stream-cdr stream))))))

;; =====================================================
;; ======================tables=========================
;; =====================================================
(define (make-table)
  (let ((local-table (list '*table*)))
    (define (lookup key-1 key-2)
      (let ((subtable (assoc key-1 (cdr local-table))))
        (if subtable
            (let ((record (assoc key-2 (cdr subtable))))
              (if record (cdr record) false))
            false)))

    (define (insert! key-1 key-2 value)
      (let ((subtable (assoc key-1 (cdr local-table))))
        (if subtable
            (let ((record (assoc key-2 (cdr subtable))))
              (if record
                  (set-cdr! record value)
                  (set-cdr! subtable
                            (cons (cons key-2 value)
                                  (cdr subtable)))))
            (set-cdr! local-table
                      (cons (list key-1 (cons key-2 value))
                            (cdr local-table)))))
      'ok)

    (define (dispatch m)
      (cond ((eq? m 'lookup-proc) lookup)
            ((eq? m 'insert-proc!) insert!)
            (else (error "Unknown operation -- TABLE" m))))
    dispatch))

(define get false)
(define put false)
;; =====================================================
;; ========= Unification and Patterns ==================
;; =====================================================

(define (make-binding variable value)
  (cons variable value))
(define (binding-variable binding) (car binding))
(define (binding-value binding) (cdr binding))
(define (binding-in-frame variable frame)
  (assoc variable frame))
(define (extend variable value frame)
  (cons (make-binding variable value) frame))
(define (tagged-list? exp tag)
  (if (pair? exp) (eq? (car exp) tag) false))
(define (var? exp)
  (tagged-list? exp '?))

; Apply the substitutions in "frame" to "expression". This is a bit like
; the Mathematica "ReplaceRepeated" or "//." operation.
(define (instantiate exp frame unbound-var-handler)
  (cond ((var? exp) 
         (let ((res (assoc exp frame)))
              (if res 
                (instantiate (cdr res) frame unbound-var-handler)
                (unbound-var-handler exp frame))))
        ((pair? exp) 
         (cons 
           (instantiate (car exp) frame unbound-var-handler)
           (instantiate (cdr exp) frame unbound-var-handler)))
         (else exp)))

(define (extend-if-consistent var dat frame)
  (let ((l (assoc var frame)))
       (if l 
         ; If it's defined, the data has to be consistent with the matched variable
         (pattern-match (cdr l) dat frame)
         ; Else, var is free for us to define.
         (extend var dat frame))))
(define (pattern-match pat dat frame)
  (cond ((eq? frame 'failed) 'failed)
        ((var? pat) (extend-if-consistent pat dat frame))
        ((and (pair? pat) (pair? dat)) 
          (let ((nf (pattern-match (car pat) (car dat) frame)))
               (if (eq? nf 'failed) 
                   'failed
                   (pattern-match (cdr pat) (cdr dat) nf))))
        ((equal? pat dat) frame)
        (else 'failed)))


(define (extend-if-possible var val frame)
  (let ((existing (binding-in-frame var frame)))
    (cond
      (existing
       (unify-match (binding-value existing) val frame))

      ((var? val)
       (let ((other (binding-in-frame val frame)))
         (if other
             (unify-match var (binding-value other) frame)
             (extend var val frame))))

      ((depends-on? val var frame)
       'failed)

      (else
       (extend var val frame)))))
(define (unify-match p1 p2 frame)
  (cond ((eq? frame 'failed) 'failed)
    ((equal? p1 p2) frame)
    ((var? p1) (extend-if-possible p1 p2 frame))
    ((var? p2) (extend-if-possible p2 p1 frame))
    ((and (pair? p1) (pair? p2))
     (unify-match
       (cdr p1)
       (cdr p2)
       (unify-match (car p1) (car p2) frame)))
    (else 'failed)))
(define (depends-on? exp var frame)
  (cond
    ((var? exp)
     (or (equal? exp var)
         (let ((binding (binding-in-frame exp frame)))
           (and binding
                (depends-on?
                  (binding-value binding)
                  var
                  frame)))))
    ((pair? exp)
     (or (depends-on? (car exp) var frame)
         (depends-on? (cdr exp) var frame)))
    (else false)))



;; ===========================================================
;; ========================Syntax / database======================
;; ===========================================================
(define (type exp)
  (if (pair? exp)
      (car exp)
      (error "Unknown expression TYPE" exp)))

(define (contents exp)
  (if (pair? exp)
      (cdr exp)
      (error "Unknown expression CONTENTS" exp)))

(define (empty-conjunction? exps) (null? exps))
(define (first-conjunct exps) (car exps))
(define (rest-conjuncts exps) (cdr exps))

(define (rule? statement)
  (tagged-list? statement 'rule))

(define (conclusion rule) (cadr rule))

(define (rule-body rule)
  (if (null? (cddr rule))
      '(always-true)
      (caddr rule)))

(define (query-syntax-process exp)
  (map-over-symbols expand-question-mark exp))

(define (map-over-symbols proc exp)
  (cond ((pair? exp)
         (cons (map-over-symbols proc (car exp))
               (map-over-symbols proc (cdr exp))))
        ((symbol? exp) (proc exp))
        (else exp)))

(define (expand-question-mark symbol)
  (let ((chars (symbol->string symbol)))
    (if (string=? (substring chars 0 1) "?")
        (list '? (string->symbol
                  (substring chars 1 (string-length chars))))
        symbol)))

(define (constant-symbol? exp) (symbol? exp))

(define rule-counter 0)

(define (new-rule-application-id)
  (set! rule-counter (+ 1 rule-counter))
  rule-counter)

(define (make-new-variable var rule-application-id)
  (cons '? (cons rule-application-id (cdr var))))

(define (contract-question-mark variable)
  (string->symbol
   (string-append
    "?"
    (if (number? (cadr variable))
        (string-append (symbol->string (caddr variable))
                       "-"
                       (number->string (cadr variable)))
        (symbol->string (cadr variable))))))

(define THE-ASSERTIONS the-empty-stream)
(define THE-RULES the-empty-stream)

(define (fetch-assertions pattern frame)
  (if (use-index? pattern)
      (get-indexed-assertions pattern)
      (get-all-assertions)))

(define (get-all-assertions) THE-ASSERTIONS)

(define (get-indexed-assertions pattern)
  (get-stream (index-key-of pattern) 'assertion-stream))

(define (get-stream key1 key2)
  (let ((s (get key1 key2)))
    (if s s the-empty-stream)))

(define (fetch-rules pattern frame)
  (if (use-index? pattern)
      (get-indexed-rules pattern)
      (get-all-rules)))

(define (get-all-rules) THE-RULES)

(define (get-indexed-rules pattern)
  (stream-append (get-stream (index-key-of pattern) 'rule-stream)
                 (get-stream '? 'rule-stream)))

(define (add-rule-or-assertion! assertion)
  (if (rule? assertion)
      (add-rule! assertion)
      (add-assertion! assertion)))

(define (add-assertion! assertion)
  (store-assertion-in-index assertion)
  (let ((old-assertions THE-ASSERTIONS))
    (set! THE-ASSERTIONS
          (cons-stream assertion old-assertions))
    'ok))

(define (add-rule! rule)
  (store-rule-in-index rule)
  (let ((old-rules THE-RULES))
    (set! THE-RULES (cons-stream rule old-rules))
    'ok))

(define (store-assertion-in-index assertion)
  (if (indexable? assertion)
      (let ((key (index-key-of assertion)))
        (let ((current-assertion-stream
               (get-stream key 'assertion-stream)))
          (put key 'assertion-stream
               (cons-stream assertion current-assertion-stream))))))

(define (store-rule-in-index rule)
  (let ((pattern (conclusion rule)))
    (if (indexable? pattern)
        (let ((key (index-key-of pattern)))
          (let ((current-rule-stream
                 (get-stream key 'rule-stream)))
            (put key 'rule-stream
                 (cons-stream rule current-rule-stream)))))))

(define (indexable? pat)
  (or (constant-symbol? (car pat))
      (var? (car pat))))

(define (index-key-of pat)
  (let ((key (car pat)))
    (if (var? key) '? key)))

(define (use-index? pat)
  (constant-symbol? (car pat)))

;; =====================================================
;; ======================qeval stuff===================
;; =====================================================

(define (qeval query frame-stream)
  (let ((qproc (get (type query) 'qeval)))
    (if qproc
        (qproc (contents query) frame-stream)
        (simple-query query frame-stream))))

(define (simple-query query-pattern frame-stream)
  (stream-flatmap
   (lambda (frame)
     (stream-append-delayed
      (find-assertions query-pattern frame)
      (delay (apply-rules query-pattern frame))))
   frame-stream))

(define (find-assertions pattern frame)
  (stream-flatmap
   (lambda (datum)
     (check-an-assertion datum pattern frame))
   (fetch-assertions pattern frame)))

(define (check-an-assertion assertion query-pat query-frame)
  (let ((match-result
         (pattern-match query-pat assertion query-frame)))
    (if (eq? match-result 'failed)
        the-empty-stream
        (singleton-stream match-result))))

(define (apply-rules pattern frame)
  (stream-flatmap
   (lambda (rule)
     (apply-a-rule rule pattern frame))
   (fetch-rules pattern frame)))

(define (always-true ignore frame-stream)
  frame-stream)


;; =====================================================
;; ======================qeval stuff===================
;; =====================================================
