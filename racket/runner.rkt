#lang racket/base
;; Runs generated module programs and prints one result line per program.
;;   racket runner.rkt server        ; framed programs on stdin: "<nbytes>\n<bytes>"
;;   racket runner.rkt file prog.rkt [variant] ; one program
;; A frame header may carry a variant: "<nbytes> <variant>\n".
;; The program text is a single `(module m racket/base ...)` form; it is
;; eval'd (compiled under whatever mode the process runs in: machine code
;; by default, interpreter under PLT_CS_INTERP=1) in a fresh namespace and
;; instantiated.  Result line (tab-separated, fields `write`n so no raw tabs
;; or newlines):
;;   ok      <output>
;;   exn     <output> <exn struct type> <first line of message>
;;   raise   <output> <written raised value>
;;   timeout <output>
;;   oom
(require racket/port racket/fixnum racket/flonum racket/unsafe/ops racket/list
         racket/string ffi/unsafe/vm)

;; Optimizer variants (third oracle, README.md "Variants"): the same module
;; compiled to machine code with one compiler toggle changed.
;;   none     default
;;   unsafe   (#%declare #:unsafe) inserted after the module header
;;   nocp0    Chez cp0 replaced by the identity (run-cp0)
;;   notr     Chez type recovery off (enable-type-recovery #f)
;;   ctx      compile-context-preservation-enabled #t (schemify inline? = #f)
;;   noconst  compile-enforce-module-constants #f
;;   cp0big   larger cp0 inlining budgets and outer-loop unrolling
;;   zo       `compile` (serializable), write + read back, eval
;;   machind  machine-independent compile, write + read back,
;;            compiled-expression-recompile, eval
;;   split    the module split in two (split-module below): provider `a` and
;;            client `m` requiring it, both eval'd in-memory (cross-module
;;            known-binding/inlining info, schemify known.rkt/find-known.rkt)
;;   splitzo  same, each module compiled, written and read back (the inline
;;            info serialized in .zo, as with raco make)
;;   splitmi  same, machine-independent compile + recompile of each module
(define VARIANTS '("none" "unsafe" "nocp0" "notr" "ctx" "noconst" "cp0big" "zo" "machind"
                   "split" "splitzo" "splitmi"))

;; Metamorphic split.  The program is `(module m racket/base <prelude>
;; <items>)`; the prelude ends with `(define-syntax-rule (show e) ...)`.
;; Module `a` = prelude + the items up to and including the last definition,
;; with `(provide (all-defined-out))`; module `m` = the prelude's `require`
;; + `(require 'a)` + the remaining items.  A module cannot `set!` an
;; imported variable, so `(set! x e)` in `m` for an `x` defined in `a`
;; becomes a call of a setter `(define (x:set v) (set! x v))` exported by
;; `a` (`set!` returns void, so does the setter).  Generated names are
;; unique (no shadowing), so the rewrite is purely syntactic.  `a` runs to
;; completion before `m`'s body, exactly as its forms ran first in the one
;; module, so output and results must be identical.
(define (split-module form)
  (define lang (caddr form))         ; racket/base
  (define forms (cdddr form))
  (define (show-def? f) (and (pair? f) (eq? (car f) 'define-syntax-rule)
                             (pair? (cadr f)) (eq? (car (cadr f)) 'show)))
  (define-values (pre items)
    (let loop ([fs forms] [acc '()])
      (cond [(null? fs) (error 'split "no prelude end")]
            [(show-def? (car fs)) (values (reverse (cons (car fs) acc)) (cdr fs))]
            [else (loop (cdr fs) (cons (car fs) acc))])))
  (define (def? f) (and (pair? f) (memq (car f) '(define define-values))))
  ;; split after the last definition: the calls of every defined function
  ;; (the generator's tail) are then all cross-module
  (define k (for/fold ([k 0]) ([f items] [i (in-naturals 1)]) (if (def? f) i k)))
  (define-values (prefix rest) (split-at items k))
  (define (defined-names f)
    (cond [(not (pair? f)) '()]
          [(eq? (car f) 'define) (list (if (pair? (cadr f)) (car (cadr f)) (cadr f)))]
          [(eq? (car f) 'define-values) (cadr f)]
          [else '()]))
  (define a-names (append-map defined-names (append pre prefix)))
  (define mutated (make-hasheq))
  (define (walk e)
    (cond [(and (pair? e) (eq? (car e) 'quote)) e]
          [(and (pair? e) (eq? (car e) 'set!) (pair? (cdr e)) (symbol? (cadr e))
                (memq (cadr e) a-names) (pair? (cddr e)) (null? (cdddr e)))
           (define setter (string->symbol (format "~a:set" (cadr e))))
           (hash-set! mutated (cadr e) setter)
           (list setter (walk (caddr e)))]
          [(pair? e) (cons (walk (car e)) (walk (cdr e)))]
          [else e]))
  (define rest* (map walk rest))
  (define reqs (filter (lambda (f) (and (pair? f) (eq? (car f) 'require))) pre))
  (define setters
    (for/list ([(x s) (in-hash mutated)])
      `(define (,s v) (set! ,x v))))
  (list `(module a ,lang (provide (all-defined-out)) ,@pre ,@prefix ,@setters)
        `(module m ,lang ,@reqs (require 'a) ,@rest*)))

(define (zo-round-trip c)
  (define o (open-output-bytes))
  (write c o)
  (parameterize ([read-accept-compiled #t])
    (read (open-input-bytes (get-output-bytes o)))))
(define chez-run-cp0 (vm-eval 'run-cp0))
(define chez-type-recovery (vm-eval 'enable-type-recovery))
(define chez-score (vm-eval 'cp0-score-limit))
(define chez-effort (vm-eval 'cp0-effort-limit))
(define chez-unroll (vm-eval 'cp0-outer-unroll-limit))

(define (variant-source variant src)
  (if (equal? variant "unsafe")
      (string-replace src "(module m racket/base\n" "(module m racket/base\n(#%declare #:unsafe)\n" #:all? #f)
      src))

;; Sets Chez-level knobs (per OS thread, so they apply to the case thread
;; too); returns a thunk that restores them.
(define (set-chez-knobs! variant)
  (define cp0 (chez-run-cp0))
  (define tr (chez-type-recovery))
  (define sc (chez-score))
  (define ef (chez-effort))
  (define un (chez-unroll))
  (case variant
    [("nocp0") (chez-run-cp0 (lambda (cp0 x) x))]
    [("notr") (chez-type-recovery #f)]
    [("cp0big") (chez-score 120) (chez-effort 5000) (chez-unroll 2)]
    [else (void)])
  (lambda ()
    (chez-run-cp0 cp0) (chez-type-recovery tr) (chez-score sc) (chez-effort ef) (chez-unroll un)))

(define TIMEOUT (let ([s (getenv "RKT_CASE_TIMEOUT")]) (if s (string->number s) 10)))
(define MAX-OUT 20000)

(define orig-ns (current-namespace))
(define real-out (current-output-port))

(define (first-line s)
  (let ([m (regexp-match #rx"^[^\n]*" s)]) (car m)))

(define (cap s) (if (> (string-length s) MAX-OUT) (substring s 0 MAX-OUT) s))

(define (fresh-ns)
  (define ns (make-base-namespace))
  (for ([m '(racket/fixnum racket/flonum racket/unsafe/ops racket/list)])
    (namespace-attach-module orig-ns m ns))
  ns)

;; Returns a list of fields.
(define (run-program src0 [variant "none"])
  (unless (member variant VARIANTS) (error 'runner "unknown variant ~a" variant))
  (define src (variant-source variant src0))
  (define out (open-output-string))
  (define cust (make-custodian))
  (custodian-limit-memory cust (* 2048 1024 1024) cust)
  (define result #f)
  (define restore! (set-chez-knobs! variant))
  (define th
    (parameterize ([current-custodian cust]
                   [compile-context-preservation-enabled (equal? variant "ctx")]
                   [compile-enforce-module-constants (not (equal? variant "noconst"))])
      (thread
       (lambda ()
         (set! result
               (parameterize ([current-namespace (fresh-ns)]
                              [current-output-port out]
                              [current-error-port out]
                              [read-accept-reader #f]
                              [read-accept-lang #f])
                 (with-handlers ([exn? (lambda (e)
                                         (list "exn" (get-output-string out)
                                               (symbol->string (vector-ref (struct->vector e) 0))
                                               ;; MASK: fixnum-overflow message wording differs by
                                               ;; mode ("with arguments" vs "computing '(fx* ..)"),
                                               ;; also in 9.3; not specified.  Kind is still compared.
                                               (if (exn:fail:contract:non-fixnum-result? e)
                                                   "<masked nonfx message>"
                                                   (first-line (exn-message e)))))]
                                 [(lambda (v) #t)
                                  (lambda (v) (list "raise" (get-output-string out)
                                                    (format "~s" v)))])
                   (define form (read (open-input-string src)))
                   (case variant
                     [("zo")
                      ;; serializable compile, written and read back as raco make does
                      (eval (zo-round-trip (compile form)))]
                     [("machind")
                      ;; machine-independent compile, round trip, recompile
                      (eval (compiled-expression-recompile
                             (zo-round-trip
                              (parameterize ([current-compile-target-machine #f])
                                (compile form)))))]
                     [("split")
                      (for ([f (split-module form)]) (eval f))]
                     [("splitzo")
                      (for ([f (split-module form)]) (eval (zo-round-trip (compile f))))]
                     [("splitmi")
                      (for ([f (split-module form)])
                        (eval (compiled-expression-recompile
                               (zo-round-trip
                                (parameterize ([current-compile-target-machine #f])
                                  (compile f))))))]
                     [else (eval form)])
                   (dynamic-require ''m #f)
                   (list "ok" (get-output-string out)))))))))
  (define done (sync/timeout TIMEOUT th))
  (custodian-shutdown-all cust)
  (restore!)
  (cond
    [(not done) (list "timeout" (get-output-string out))]
    [(not result) (list "oom")]
    [else result]))

(define (emit fields)
  (define strs
    (for/list ([f fields] [i (in-naturals)])
      (if (zero? i) f (format "~s" (cap f)))))
  (write-string (string-join* strs "\t") real-out)
  (newline real-out)
  (flush-output real-out))

(define (string-join* l sep)
  (apply string-append (add-between l sep)))

(define args (current-command-line-arguments))
(cond
  [(and (= (vector-length args) 1) (equal? (vector-ref args 0) "server"))
   (let loop ()
     (define line (read-line (current-input-port) 'linefeed))
     (unless (eof-object? line)
       (define parts (string-split line))
       (define n (string->number (car parts)))
       (define variant (if (pair? (cdr parts)) (cadr parts) "none"))
       (define bs (read-bytes n (current-input-port)))
       (emit (run-program (bytes->string/utf-8 bs #\?) variant))
       (loop)))]
  [(and (<= 2 (vector-length args) 3) (equal? (vector-ref args 0) "file"))
   (emit (run-program (call-with-input-file (vector-ref args 1) port->string)
                      (if (= (vector-length args) 3) (vector-ref args 2) "none")))]
  [(and (= (vector-length args) 2) (equal? (vector-ref args 0) "splitdump"))
   ;; prints the two modules of the split variants (for triage)
   (for ([f (split-module (read (open-input-string
                                 (call-with-input-file (vector-ref args 1) port->string))))])
     (write f real-out) (newline real-out))]
  [else (error 'runner "usage: runner.rkt server | file <prog> [variant]")])
