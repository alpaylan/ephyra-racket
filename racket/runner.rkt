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
         racket/string racket/pretty ffi/unsafe/vm)

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
;;   macro    the items rewritten through hygienic macros (macro-module below)
;;   macrozo  same, compiled, written and read back (serialized scope sets,
;;            binding tables and macro templates)
;;   macrosplit  split first, then rewritten; the macros are defined in `a`
;;            and used by `m` after a zo round trip of `a` (imported macros,
;;            shifted multi-scopes, deserialized syntax)
(define VARIANTS '("none" "unsafe" "nocp0" "notr" "ctx" "noconst" "cp0big" "zo" "machind"
                   "split" "splitzo" "splitmi" "macro" "macrozo" "macrosplit"))

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

;; ---------------------------------------------------------------------
;; Metamorphic macro rewrite (variants macro, macrozo, macrosplit; steering
;; round 4).  The generated items are rewritten through hygienic macros
;; defined in the module itself (or, for macrosplit, in the provider module
;; `a` and imported by `m`).  Every macro expands to exactly the form it
;; replaces plus bindings the user code cannot see (hygiene: the
;; introduced binders deliberately reuse names of the program's own
;; variables, prelude names like `tap`/`mv`, and `tmp`), and every template
;; keeps the user expression in tail position of the expansion, so
;; continuation marks and tail calls are unchanged.  Constructs: wrappers
;; for if/let/let*/named let/lambda/set!/application/define (module level
;; and internal: definitions produced by macro uses, use-site scopes),
;; macro-defining macros with nested ellipses, recursive macros that wrap
;; an expression in up to 40 lets (large scope sets: the scope-set
;; representation of f1a34e208d), define-syntax in internal-definition
;; contexts, set!-transformers standing for function parameters.  Generated
;; names are unique and never shadow a primitive, so the rewrite is purely
;; syntactic and the result must equal the unrewritten module's.  Choices
;; are a deterministic function of the program text.
(define base-procs
  (let ([ns (make-base-namespace)])
    (parameterize ([current-namespace ns])
      (namespace-require 'racket/fixnum)
      (namespace-require 'racket/flonum))
    (lambda (s)
      (with-handlers ([(lambda (e) #t) (lambda (e) #f)])
        (procedure? (parameterize ([current-namespace ns])
                      (namespace-variable-value s #t (lambda () #f))))))))

(define (macro-rng src)
  (define st (for/fold ([h 7]) ([c (in-string src)])
               (bitwise-and (+ (* h 31) (char->integer c)) #xFFFFFFFF)))
  (lambda (n)                           ; 0 .. n-1
    (set! st (bitwise-and (+ (* st 1103515245) 12345) #x7FFFFFFF))
    (modulo (arithmetic-shift st -8) n)))

;; names: every (define (name ...)) and [name (lambda ...)] in the program
(define (user-fn-names forms)
  (define acc (make-hasheq))
  (let walk ([e forms])
    (when (pair? e)
      (cond [(eq? (car e) 'quote) (void)]
            [else
             (when (and (eq? (car e) 'define) (pair? (cdr e)) (pair? (cadr e)) (symbol? (car (cadr e))))
               (hash-set! acc (car (cadr e)) #t))
             (when (and (symbol? (car e)) (pair? (cdr e)) (pair? (cadr e)) (eq? (car (cadr e)) 'lambda))
               (hash-set! acc (car e) #t))
             (walk (car e)) (walk (cdr e))])))
  acc)

(define (var-names forms)
  (define acc (make-hasheq))
  (let walk ([e forms])
    (cond [(and (pair? e) (eq? (car e) 'quote)) (void)]
          [(pair? e) (walk (car e)) (walk (cdr e))]
          [(and (symbol? e) (regexp-match? #rx"^[a-z]+[0-9]+$" (symbol->string e)))
           (hash-set! acc e #t)]
          [else (void)]))
  (sort (hash-keys acc) symbol<?))

;; Macro definitions; `cn` = collision names for introduced binders.
(define (macro-defs cn)
  (define (n i) (list-ref cn (modulo i (length cn))))
  `((define-syntax-rule (m-def-if name N)
      (define-syntax-rule (name c t e) (let ([N c]) (if N t e))))
    (m-def-if m-if ,(n 0))
    (define-syntax-rule (m-def-app name N)
      (define-syntax name
        (syntax-rules ()
          [(_ f a (... ...)) (let ([N 0]) (f a (... ...)))])))
    (m-def-app m-app ,(n 1))
    (define-syntax (m-app2 stx)
      (syntax-case stx ()
        [(_ f a ...) (with-syntax ([(t ...) (generate-temporaries #'(a ...))])
                       #'(#%app f a ...))]))
    (define-syntax m-let
      (syntax-rules ()
        [(_ ([x e] ...) b ...) (let-values ([(x) e] ...) (let ([,(n 2) 'm-let]) b ...))]))
    (define-syntax m-let*
      (syntax-rules ()
        [(_ () b ...) (let () b ...)]
        [(_ ([x e] r ...) b ...) (let ([x e]) (m-let* (r ...) b ...))]))
    (define-syntax-rule (m-nlet name ([x e] ...) b ...)
      (let ([,(n 3) 'm-nlet]) (let name ([x e] ...) b ...)))
    (define-syntax-rule (m-lambda args b ...)
      (lambda args (define ,(n 4) 'm-lambda) b ...))
    (define-syntax (m-set! stx)
      (syntax-case stx ()
        [(_ x e) (identifier? #'x) #'(let ([,(n 5) e]) (set! x ,(n 5)))]))
    (define-syntax-rule (m-def x e) (begin (define ,(n 6) 'm-def) (define x e)))
    (define-syntax m-define
      (syntax-rules ()
        [(_ (f . args) b ...) (begin (define ,(n 7) 'm-define) (define (f . args) b ...))]))
    (define-syntax (m-deep stx)
      (syntax-case stx ()
        [(_ k e) (let ([k* (syntax-e #'k)])
                   (if (zero? k*)
                       #'e
                       (with-syntax ([km (sub1 k*)])
                         #'(let ([,(n 8) k]) (m-deep km e)))))]))
    (define-syntax-rule (m-tap e) (let ([tap 'm-tap] [mv 'm-tap] [tmp 'm-tap]) e))
    ;; scope operations on the argument that must cancel out: an introducer
    ;; applied twice (flip), syntax-local-introduce twice, and rebuilding
    ;; the argument with datum->syntax from its own (uniform) context
    (define-syntax (m-flip stx)
      (syntax-case stx ()
        [(_ e) (let ([intro (make-syntax-introducer)])
                 (with-syntax ([e* (intro (intro #'e))])
                   #'(let ([,(n 9) 'm-flip]) e*)))]))
    (define-syntax (m-lintro stx)
      (syntax-case stx ()
        [(_ e) (with-syntax ([e* (syntax-local-introduce (syntax-local-introduce #'e))])
                 #'(let ([,(n 10) 'm-lintro]) e*))]))
    (define-syntax (m-reflect stx)
      (syntax-case stx ()
        [(_ e) (with-syntax ([e* (datum->syntax #'e (syntax->datum #'e) #'e #'e)])
                 #'(let ([,(n 11) 'm-reflect]) e*))]))))

(define (macro-rewrite-items items all-forms rng)
  (define fns (user-fn-names all-forms))
  (define (proc-head? s) (and (symbol? s) (or (hash-ref fns s #f) (base-procs s))))
  (define (pick k) (zero? (rng k)))          ; probability 1/k
  (define (maybe k) (< (rng 10) k))          ; probability k/10
  (define gensym-n 0)
  (define (fresh base) (set! gensym-n (add1 gensym-n))
    (string->symbol (format "~a~~m~a" base gensym-n)))
  ;; ren: symbol -> replacement identifier (set!-transformer macros)
  (define (wrap-arg e ren)
    (define e* (ex e ren))
    (cond [(pick 12) `(m-deep ,(add1 (rng 40)) ,e*)]
          [(pick 15) `(m-tap ,e*)]
          [(pick 25) `(,(case (rng 3) [(0) 'm-flip] [(1) 'm-lintro] [else 'm-reflect]) ,e*)]
          [else e*]))
  (define (body bs ren) (map (lambda (b) (ex b ren)) bs))
  (define (bindings bs ren)
    (for/list ([b bs]) (list (car b) (ex (cadr b) ren))))
  (define (clauses-ok? bs) (and (list? bs) (andmap (lambda (b) (and (list? b) (= 2 (length b)) (symbol? (car b)))) bs)))
  (define (fn-body args bs ren)
    ;; function body: some parameters become set!-transformer macros
    (define params (let loop ([a args]) (cond [(pair? a) (cons (car a) (loop (cdr a)))]
                                              [(symbol? a) (list a)] [else '()])))
    (define chosen (filter (lambda (p) (maybe 4)) params))
    (define ren* (for/fold ([r ren]) ([p chosen]) (hash-set r p (fresh p))))
    (define defs
      (for/list ([p chosen])
        (define m (hash-ref ren* p))
        `(define-syntax ,m
           (make-set!-transformer
            (lambda (stx)
              (syntax-case stx (set!)
                [(set! id~ v~) #'(set! ,p v~)]
                [(id~ a~ ...) #'(,p a~ ...)]
                [id~ (identifier? #'id~) #',p]))))))
    (append defs (body bs ren*)))
  (define (ex e ren)
    (cond
      [(symbol? e) (hash-ref ren e e)]
      [(not (pair? e)) e]
      [(not (list? e)) e]
      [else
       (define h (car e))
       (define n (length e))
       (case h
         [(quote) e]
         [(if) (if (= n 4)
                   (let ([c (wrap-arg (cadr e) ren)] [t (ex (caddr e) ren)] [f (ex (cadddr e) ren)])
                     (if (maybe 6) `(m-if ,c ,t ,f) `(if ,c ,t ,f)))
                   e)]
         [(begin and or when unless show writeln)
          `(,h ,@(body (cdr e) ren))]
         [(with-continuation-mark)
          `(,h ,@(body (cdr e) ren))]
         [(let)
          (cond
            [(and (>= n 3) (symbol? (cadr e)) (clauses-ok? (caddr e)))
             `(,(if (maybe 5) 'm-nlet 'let) ,(cadr e) ,(bindings (caddr e) ren) ,@(body (cdddr e) ren))]
            [(and (>= n 3) (clauses-ok? (cadr e)))
             `(,(if (maybe 5) 'm-let 'let) ,(bindings (cadr e) ren) ,@(body (cddr e) ren))]
            [else e])]
         [(let* letrec)
          (if (and (>= n 3) (clauses-ok? (cadr e)))
              `(,(if (and (eq? h 'let*) (maybe 5)) 'm-let* h) ,(bindings (cadr e) ren) ,@(body (cddr e) ren))
              e)]
         [(let-values)
          (if (>= n 3)
              `(let-values ,(for/list ([b (cadr e)]) (list (car b) (ex (cadr b) ren))) ,@(body (cddr e) ren))
              e)]
         [(lambda)
          (if (>= n 3)
              `(,(if (maybe 4) 'm-lambda 'lambda) ,(cadr e) ,@(body (cddr e) ren))
              e)]
         [(define)
          (cond [(and (pair? (cadr e)) (>= n 3))
                 `(,(if (maybe 5) 'm-define 'define) ,(cadr e) ,@(fn-body (cdr (cadr e)) (cddr e) ren))]
                [(and (symbol? (cadr e)) (= n 3))
                 `(,(if (maybe 5) 'm-def 'define) ,(cadr e) ,(ex (caddr e) ren))]
                [else e])]
         [(define-values)
          (if (= n 3) `(define-values ,(cadr e) ,(ex (caddr e) ren)) e)]
         [(set!)
          (if (and (= n 3) (symbol? (cadr e)))
              `(,(if (maybe 6) 'm-set! 'set!) ,(hash-ref ren (cadr e) (cadr e)) ,(ex (caddr e) ren))
              e)]
         [(cond)
          `(cond ,@(for/list ([c (cdr e)])
                     (if (list? c)
                         (map (lambda (x) (if (memq x '(else =>)) x (ex x ren))) c)
                         c)))]
         [(case)
          (if (>= n 2)
              `(case ,(ex (cadr e) ren)
                 ,@(for/list ([c (cddr e)])
                     (if (and (list? c) (pair? c)) (cons (car c) (body (cdr c) ren)) c)))
              e)]
         [(with-handlers parameterize)
          (if (and (>= n 3) (list? (cadr e)) (andmap (lambda (c) (and (list? c) (= 2 (length c)))) (cadr e)))
              `(,h ,(for/list ([c (cadr e)]) (list (ex (car c) ren) (ex (cadr c) ren))) ,@(body (cddr e) ren))
              e)]
         [(for/sum for/list for)
          (if (and (>= n 3) (clauses-ok? (cadr e)))
              `(,h ,(bindings (cadr e) ren) ,@(body (cddr e) ren))
              e)]
         [(for/fold)
          (if (and (>= n 4) (clauses-ok? (cadr e)) (clauses-ok? (caddr e)))
              `(,h ,(bindings (cadr e) ren) ,(bindings (caddr e) ren) ,@(body (cdddr e) ren))
              e)]
         [else
          (cond
            [(or (proc-head? h) (hash-ref ren h #f)
                 (and (symbol? h) (regexp-match? #rx"^[a-z]+[0-9]+$" (symbol->string h))))
             (define args (map (lambda (a) (wrap-arg a ren)) (cdr e)))
             (define f (hash-ref ren h h))
             (case (rng 10)
               [(0 1 2) `(m-app ,f ,@args)]
               [(3) `(m-app2 ,f ,@args)]
               [else `(,f ,@args)])]
            [(pair? h)                     ; ((lambda ...) args) etc.
             (map (lambda (a) (ex a ren)) e)]
            [else e])])]))   ; unknown syntactic form: unchanged
  (map (lambda (it) (ex it (hash))) items))

;; `quote-syntax-dummy` placeholder: the identifier case of the
;; set!-transformer expands to the parameter itself.
(define (fix-dummy d)
  (let walk ([e d])
    (cond [(and (pair? e) (eq? (car e) 'quote-syntax-dummy)) (cadr e)]
          [(pair? e) (cons (walk (car e)) (walk (cdr e)))]
          [else e])))

(define (split-prelude forms)
  (define (show-def? f) (and (pair? f) (eq? (car f) 'define-syntax-rule)
                             (pair? (cadr f)) (eq? (car (cadr f)) 'show)))
  (let loop ([fs forms] [acc '()])
    (cond [(null? fs) (error 'macro "no prelude end")]
          [(show-def? (car fs)) (values (reverse (cons (car fs) acc)) (cdr fs))]
          [else (loop (cdr fs) (cons (car fs) acc))])))

(define (macro-cn all src)
  (define vs (var-names all))
  (append (if (null? vs) '(x0) vs) '(tmp tap mv)))

;; single module: (module m racket/base <prelude> <macro defs> <items'>)
(define (macro-module form src)
  (define lang (caddr form))
  (define-values (pre items) (split-prelude (cdddr form)))
  (define rng (macro-rng src))
  (define cn (macro-cn (cdddr form) src))
  (define cn* (shuffle-det cn rng))
  `(module m ,lang (require (for-syntax racket/base)) ,@pre ,@(macro-defs cn*)
     ,@(macro-rewrite-items items (cdddr form) rng)))

(define (shuffle-det l rng)
  (let loop ([l l] [acc '()])
    (if (null? l) acc
        (let ([x (list-ref l (rng (length l)))])
          (loop (remq x l) (cons x acc))))))

;; split first (setters for set! across modules), then rewrite both; the
;; macros live in `a` and are exported by (all-defined-out) to `m`.
(define (macro-split form src)
  (define ms (split-module form))
  (define a (car ms))
  (define m (cadr ms))
  (define rng (macro-rng src))
  (define cn (shuffle-det (macro-cn (cdddr form) src) rng))
  ;; a = (module a lang (provide (all-defined-out)) <pre> <prefix> <setters>)
  (define-values (a-pre a-items) (split-prelude (cdr (cdddr a))))
  (define a-lang (caddr a))
  (define all (cdddr form))
  (list `(module a ,a-lang (require (for-syntax racket/base)) (provide (all-defined-out))
           ,@a-pre ,@(macro-defs cn) ,@(macro-rewrite-items a-items all rng))
        `(module m ,(caddr m) (require (for-syntax racket/base))
           ,@(macro-rewrite-items (cdddr m) all rng))))

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
                     [("macro") (eval (macro-module form src))]
                     [("macrozo") (eval (zo-round-trip (compile (macro-module form src))))]
                     [("macrosplit")
                      (for ([f (macro-split form src)]) (eval (zo-round-trip (compile f))))]
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
  [(and (= (vector-length args) 3) (equal? (vector-ref args 0) "macrodump"))
   ;; prints the rewritten module(s) of the macro variants (for triage)
   (let* ([src (call-with-input-file (vector-ref args 1) port->string)]
          [form (read (open-input-string src))])
     (for ([f (if (equal? (vector-ref args 2) "macrosplit")
                  (macro-split form src)
                  (list (macro-module form src)))])
       (pretty-write f real-out)))]
  [else (error 'runner "usage: runner.rkt server | file <prog> [variant]")])
