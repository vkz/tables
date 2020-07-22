#lang racket


(require racket/struct
         racket/generic
         syntax/parse/define
         (for-syntax syntax/parse
                     racket/match)
         (only-in racket
                  [#%top racket/#%top]
                  [#%app racket/#%app]))


(require (only-in prelude ht get: set:))


(provide (rename-out [#%top table-#%top] [#%app table-#%app]
                     [table-instance table])
         #%table #%: : ::
         get set rm meta-dict-ref
         isa isa?
         table?
         table-meta table-dict
         set-meta
         set-table-meta! set-table-dict!
         <table>
         <spec> <open> <closed>
         required optional req opt
         <tables>
         <table/evt>
         tag?
         define/table
         (all-from-out 'logic))


(module+ test
  (require rackunit)
  (require prelude/testing))


(begin-for-syntax
  (require racket/logging)
  (define (log v)
    (with-logging-to-port (current-output-port)
      (λ () (log-debug "~a" v))
      'debug)))


;;* Undefined aware logic ---------------------------------------- *;;


(module logic racket

  (require racket/undefined)
  (provide (all-defined-out) undefined)


  (define (? v [when-undefined #f])
    (if (eq? undefined v) when-undefined v))


  (define (undefined? e)
    (eq? undefined e))


  (define (some? val)
    ;; should I also treat null as #f?
    (if (undefined? val) #f val))


  (define (none? val)
    (not (some? val)))


  (define-syntax or?
    (syntax-rules ()
      ((_ e) e)
      ((_ e1 e ...) (or (some? e1) (or? e ...)))))


  (define-syntax and?
    (syntax-rules ()
      ((_ e) e)
      ((_ e1 e ...) (let ((test e1))
                      (if (some? test) (and? e ...) test)))))


  (define-syntax-rule (if? test then else)
    (if (some? test) then else))


  (define-syntax-rule (when? test body ...)
    (when (some? test) body ...))


  (define-syntax-rule (unless? test body ...)
    (when (none? test) body ...))

  ;; TODO cond?
  ;; TODO when-let, if-let
  )


(require 'logic)


(module+ test
  (test-case "undefined aware logic"

    ;; ?
    (check-false (? undefined))
    (check-true (? undefined #t))
    (check-eq? (? 42) 42)
    (check-eq? (? 42 #f) 42)
    (check-false (? #f #t))

    ;; or?
    (check-eq? (or? undefined #f 42) 42)
    (check-eq? (or? 42) 42)
    (check-eq? (or? #f) #f)
    (check-eq? (or? undefined) undefined)
    (check-eq? (or? #f undefined) undefined)
    (check-eq? (or? undefined #f undefined) undefined)

    ;; and?
    (check-eq? (and? 42) 42)
    (check-eq? (and? #f) #f)
    (check-eq? (and? undefined) undefined)
    (check-eq? (and? undefined #f undefined) undefined)

    ;; or? and? combined
    (check-eq? (and? (or? undefined 42) (or? undefined) 42) undefined)))


;;* :tags -------------------------------------------------------- *;;


(begin-for-syntax

  (define-values (re-tag? re-method? re-colon? re-colon-colon?)
    (let* ((tag         #px"^:[^:]\\S*$")
           (method      #px"^::[^:]\\S*$")
           (colon       #px"^:$")
           (colon-colon #px"^::$")
           (stx->str    (compose symbol->string syntax->datum)))
      (define ((re? rx) stx) (regexp-match rx (stx->str stx)))
      (values (re? tag) (re? method) (re? colon) (re? colon-colon))))

  (define-syntax-class tag         (pattern id:id #:when (re-tag? #'id)))
  (define-syntax-class method      (pattern id:id #:when (re-method? #'id)))
  (define-syntax-class colon       (pattern id:id #:when (re-colon? #'id)))
  (define-syntax-class colon-colon (pattern id:id #:when (re-colon-colon? #'id)))

  (define (method->tag stx)
    (define tag
      (string->symbol
       (if (re-method? stx)
           (substring (symbol->string (syntax->datum stx)) 1)
           (raise-argument-error 'method->tag "syntax for ::method identifier" stx))))
    ;; TODO should we use #%datum from macro-invocation context?
    #`(#%datum . #,tag))

  ;; TODO I am not sure this covers every possibility, but AFAIK since we are
  ;; using it in #%app transformers will have been expanded. Better check with
  ;; core racketeers.
  (define (unbound? stx)
    (define top-level-or-unbound (not (identifier-binding stx)))
    (define not-top-level-bound (not (identifier-binding stx (syntax-local-phase-level) #t)))
    (and top-level-or-unbound))

  (define-syntax-class free-id (pattern id:id #:when (unbound? #'id))))


(define (tag? t)
  (and (symbol? t)
       (string-prefix? (symbol->string t) ":")))


;;* #%: ---------------------------------------------------------- *;;


(begin-for-syntax

  (define (table-sep-key? id . seps)
    (define (rx sep) (format "^(.+)~a(.+)$" (regexp-quote sep)))
    (define idstr (symbol->string (syntax->datum id)))
    (for/or ((sep (in-list seps)))
      (match idstr
        ((regexp (rx sep) (list _ table key))
         ;; => (list "sep" "table" "key")
         (list sep table key))
        (else #f))))

  (define-syntax-class (table-sep-key sep)
    (pattern id:id
             #:attr split (table-sep-key? #'id sep)
             #:when (attribute split)
             #:do [(match-define (list sep table key) (attribute split))]
             #:with table (datum->syntax #'id (string->symbol table) #'id)
             #:with tag   (datum->syntax #'id (string->symbol (format ":~a" key)) #'id)
             #:with sym   (datum->syntax #'id (string->symbol key) #'id))))


(define-syntax-parser #%:
  ((_ ":" (~var id (table-sep-key ":")))
   (syntax/loc #'id (or? (get id.table 'id.tag)
                         (get id.table 'id.sym)
                         ;; TODO consider also looking up string key
                         ;; (get id.table 'id.str)
                         )))

  ((_ "::" (~var id (table-sep-key "::")))
   (syntax/loc #'id
     (let ((proc (or? (get id.table 'id.tag)
                      (get id.table 'id.sym))))
       (unless (procedure? proc)
         (raise-result-error 'id "procedure?" proc))
       (make-keyword-procedure
        (λ (kws kw-args . rest) (keyword-apply proc kws kw-args id.table rest))
        (λ args (apply proc id.table args)))))))


;;* #%top -------------------------------------------------------- *;;


(define-syntax (#%top stx)
  (syntax-parse stx

    ((_ . id:id)
     ;; table:key =>
     #:attr split (table-sep-key? #'id "::" ":")
     #:when (attribute split)
     #:with sep (car (attribute split))
     #:with #%: (datum->syntax #'id '#%: #'id)
     (syntax/loc #'id (#%: sep id)))

    ((_ . id:tag)
     ;; :tag =>
     (syntax/loc stx (#%datum . id)))

    ((_ . id:id)
     ;; id =>
     (syntax/loc stx (racket/#%top . id)))

    (_ (raise-syntax-error '#%top "invalid syntax in top"))))


(module+ test
  (test-case "t:k and t::k accessors"
    (define <proc> {(:<proc> (λ (mt t k) (get t k)))})
    (define proc {<proc>})
    (define t {(:a 1)
               ;; procedure
               (:f (λ (t k) (get t k)))
               ;; struct procedure
               (:proc proc)})
    (check-eq? t:a 1)
    (check-eq? (t:f t :a) 1)
    (check-eq? (t::f :a) 1)
    (check-eq? (t:proc t :a) 1)
    (check-eq? (t::proc :a) 1)))


;;* table struct ------------------------------------------------- *;;


;; NOTE Replace apply with keyword-apply if some dict method takes kw args
(define ((redirect-generic generic) t . args)
  (apply generic (table-dict t) args))


(define (meta-dict-ref t key)
  (define mt (table-meta t))
  (if (table? mt) (dict-ref mt key) undefined))


(define table-procedure
  (make-keyword-procedure
   (λ (kws kw-args t . rest)
     (let ((proc (meta-dict-ref t :<proc>)))
       (if (procedure? proc)
           ;; NOTE t here will always be bound to the table that was invoked as
           ;; procedure i.e. table whose metatable specifies (:<proc> proc) - a
           ;; consequence of how Racket prop::procedure operates. This means that
           ;; proc must be a procedure of at least one argument.
           (keyword-apply proc kws kw-args t rest)
           (error "table has no <proc> metamethod to apply"))))))


(struct table (dict meta)
  #:mutable
  ;; NOTE We make table struct #:transparent for now to avoid the need for custom
  ;; gen:equal+hash interface. Basically, we fallback on the default equal? Would
  ;; need to revisit if this becomes a perf bottleneck or table semantics changes.
  #:transparent
  #:constructor-name make-table

  #:property prop:procedure table-procedure

  #:methods gen:dict
  ((define/generic ref           dict-ref)
   (define/generic set!          dict-set!)
   (define/generic has-key?      dict-has-key?)
   (define/generic remove!       dict-remove!)
   (define/generic iterate-first dict-iterate-first)
   (define/generic iterate-next  dict-iterate-next)
   (define/generic iterate-key   dict-iterate-key)
   (define/generic iterate-value dict-iterate-value)

   (define (dict-ref t k [default (λ () undefined)])
     (ref (table-dict t) k default))

   (define (dict-set! t k v)
     (define dict (table-dict t))
     (if (undefined? v) (remove! dict k) (set! dict k v)))

   (define dict-has-key?      (redirect-generic has-key?))
   (define dict-remove!       (redirect-generic remove!))
   (define dict-iterate-first (redirect-generic iterate-first))
   (define dict-iterate-next  (redirect-generic iterate-next))
   (define dict-iterate-key   (redirect-generic iterate-key))
   (define dict-iterate-value (redirect-generic iterate-value)))

  #:methods gen:custom-write
  ((define write-proc
     (make-constructor-style-printer
      (λ (t) 'table)
      (λ (t) (for/list (((k v) (in-dict (table-dict t))))
               (list k v)))))))


(module+ test

  (test-case "<proc>"
    (define <proc> (make-table (ht (:<proc> dict-ref)) undefined))
    (define <kwproc> (make-table (ht (:<proc> (λ (t #:key key) (dict-ref t key)))) undefined))
    (check-eq? ((make-table (ht (:a 1)) <proc>) :a) 1)
    (check-eq? ((make-table (ht (:a 1)) <kwproc>) #:key :a) 1)
    (check-exn exn? (thunk ((make-table (ht) undefined) 1)) "table has no <proc>"))

  (test-case "equality"
    (define <mt> {(:b 2)})
    (check-true (equal? {} {}))
    (check-true (equal? {<mt> (:a 1)} {<mt> (:a 1)}))
    (check-false (equal? {(:a 1)} {}))))


(module+ test

  (test-case "gen:dict"
    (define t (make-table (ht (:a 1)) undefined))
    (check-true (dict-has-key? t :a))
    (check-eq? (dict-ref t :a) 1)
    (check-true (undefined? (dict-ref t :b)))
    (check-not-exn (thunk (dict-set! t :b 2)))
    (check-eq? (dict-ref t :b) 2))

  (test-case "gen:associative"
    (define tb (make-table (ht (:b 1)) undefined))
    (define ta (make-table (ht (:a tb)) undefined))
    (check-eq? (get: ta :a :b) 1)
    (check-not-exn (thunk (set: ta :a :c 2)))
    (check-eq? (get: ta :a :c) 2)))


;;* get ---------------------------------------------------------- *;;


;; TODO IMO this is where top, self (or this) ought to be bound and
;; propagated. Fix point or lazy values maybe easiest to explicitly
;; wrap a-la {:k (delay (top this) compute value)} which is merely a
;; function or itself a table. When get arrives at delayed value it
;; forces it while passing the top-most table as well as table where
;; key's been found to to delay (just a lambda of two parameters).
(define (get t k)
  (if (dict-has-key? t k)
      (dict-ref t k)
      (let ((mt (table-meta t))
            ;; we rely on meta-dict-ref returning undefined when mt is not a table
            (metamethod (meta-dict-ref t :<get>)))
        (cond
          ((table? metamethod) (get metamethod k))
          ((procedure? metamethod) (metamethod t k))
          ;; TODO ^^^ (matmethod t k) has t bound to "this" i.e. table
          ;; with :<get> metamethod - not necessarily top-most table.
          ;; Mistake when :<get> is found further down the chain?
          ;; Ought to propagate both "top" and "this".
          ((undefined? metamethod) (if (table? mt) (get mt k) undefined))
          (else (raise-argument-error '<get> "table or procedure" metamethod))))))


;;* isa? --------------------------------------------------------- *;;

;; TODO shoud we rename these into meta and meta? respectively?

;; TODO built-ins
(define (isa t) (table-meta t))


(define (isa? t <mt>)
  ;; TODO built-ins
  (define mt (table-meta t))
  (define metamethod (meta-dict-ref t :<isa?>))
  ;; TODO should we check (eq? t <mt>)? Kinda makes sense but it would be
  ;; inconsistent with our isa definition above.
  (or (eq? mt <mt>)
      (cond
        ((table? metamethod) (or (eq? metamethod <mt>) (isa? metamethod <mt>)))
        ((procedure? metamethod) (t::<isa?> <mt>))
        ((undefined? metamethod) #f)
        (else (raise-argument-error '<isa?> "table or procedure" metamethod)))
      ;; continue search up the metatable chain
      (and
       (table? mt)
       (isa? mt <mt>))))


(module+ test
  (define/checked <mt0> {})
  (define/checked <mt1> {<mt0>})
  (define/checked <mt2> {(:<isa?> <mt1>)})
  (define/checked <mt3> {(:<isa?> (λ (self mt) (or (eq? <mt2> mt) (eq? <mt1> mt))))})
  (check-true (isa? {} <table>))

  (check-true (isa? <mt0> <table>))
  (check-true (isa? {<mt0>} <mt0>))

  (check-true (isa? {<mt1>} <mt0>))
  (check-true (isa? {<mt1>} <table>))

  (check-true (isa? <mt2> <table>))
  (check-false (isa? <mt2> <mt1>))
  (check-true (isa? {<mt2>} <mt2>))
  (check-true (isa? {<mt2>} <mt1>))
  (check-true (isa? {<mt2>} <mt0>))

  (check-true (isa? {<mt3>} <mt3>))
  (check-true (isa? {<mt3>} <mt2>))
  (check-true (isa? {<mt3>} <mt1>))
  (check-false (isa? {<mt3>} <mt0>)))


;;* set ---------------------------------------------------------- *;;


;; NOTE set : (table? k v . -> . table?) which means <set> metamethod must comply
;; with that contract
(define (set t k v)
  (define metamethod (meta-dict-ref t :<set>))
  (cond
    ;; TODO is this too much, should we dict-set! to cut recursion?
    ((table? metamethod) (set metamethod k v))
    ((procedure? metamethod) (metamethod t k v))
    ((undefined? metamethod) (dict-set! t k v) t)
    (else (raise-argument-error '<set> "table or procedure" metamethod))))


(define (rm t k) (set t k undefined))


(module+ test

  (define/checked mt (make-table (ht (:b 2)) undefined))
  (define/checked t (make-table #;t (ht (:a 1)) #;mt mt))
  (define/checked tt (make-table #;t (ht) #;mt t))
  (define/checked t<get>proc (make-table #;t (ht) #;mt (make-table (ht (:<get> (λ (_ key) (get t key)))) undefined)))
  (define/checked t<get>table (make-table #;t (ht) #;mt (make-table (ht (:<get> t)) undefined)))

  (test-case "get: when mt is a table"
    (check-eq? (get t :a) 1)
    (check-eq? (get t :b) 2)
    (check-pred undefined? (get t :c))
    ;; deeper mt chain
    (check-eq? (get tt :a) 1)
    (check-eq? (get tt :b) 2)
    (check-pred undefined? (get tt :c)))

  (test-case "get: when <get> metamethod is a procedure"
    (check-eq? (get t<get>proc :a) 1)
    (check-eq? (get t<get>proc :b) 2)
    (check-pred undefined? (get t<get>proc :c)))

  (test-case "get: when <get> metamethod is a table"
    (check-eq? (get t<get>table :a) 1)
    (check-eq? (get t<get>table :b) 2)
    (check-pred undefined? (get t<get>table :c)))

  (test-case "set: with no <set> metamethod"
    ;; insert
    (check-not-exn (thunk (set t :c 3)))
    (check-eq? (get t :c) 3)
    ;; update
    (check-not-exn (thunk (set t :a 0)))
    (check-eq? (get t :a) 0))

  (test-case "set: when <set> is a table"
    (check-not-exn (thunk (set mt :<set> mt)))
    ;; insert
    (check-not-exn (thunk (set t :d 4)))
    (check-eq? (get mt :d) 4)
    (check-eq? (get t :d) 4)
    ;; update inserted
    (check-not-exn (thunk (set t :d 0)))
    (check-eq? (get mt :d) 0)
    ;; update existing
    (check-not-exn (thunk (set t :a -1)))
    (check-eq? (get t :a) 0)
    (check-eq? (get mt :a) -1))

  (test-case "set: when <set> is a procedure"
    (check-not-exn (thunk (set mt :<set> (λ (_ k v) (set mt k v)))))
    (check-not-exn (thunk (set t :e 5)))
    (check-eq? (get mt :e) 5)
    (check-eq? (get t :e) 5)))


;;* Constructors ------------------------------------------------- *;;


(define <table> (make-table (ht) undefined))


;; Similar to set-table-meta! but ensures that <setmeta> method of the new
;; metatable runs when present
(define/contract (set-meta t mt)
  (-> table? table? table?)
  (define metamethod (or? (dict-ref mt :<setmeta>) identity))
  (set-table-meta! t mt)
  (metamethod t))


;; TODO consider implementing set-dict which is like set-table-dict! but it must
;; preserve the same table struct type, trim possible undefined values and call
;; <setmeta> when present. Essentially it does what #%table's expansion does. We
;; maybe able to replace part of #%table's expansion with a call to set-dict.


(begin-for-syntax

  (define-splicing-syntax-class option
    ;; #:attributes ((kw 1) (opt 1))
    (pattern
     (~describe #:role "keyword option pair"
                "#:kw expr"
                (~seq kw:keyword opt:expr))))


  (define-syntax-class table-entry
    #:attributes (key value)
    (pattern
     (~describe #:role "table entry"
                "(key value) pair"
                ((~and key:expr (~not (~literal quote))) value:expr)))))


;; TODO #:kw trait is either a table whose action is encoded in the :<setmeta>
;; method (not metamethod), or a procedure. I am uneasy about the whole thing
;; particularly table + <setmeta> idea, mostly because without extra work this
;; trait's <setmeta> doesn't have access to the trait. But if such cases are rare
;; (e.g. <spec>) then we can always do the same indirection trick: <setmeta>
;; metamethod installs trait's <setmeta> that closes over the trait.


(define (add-traits t opts)
  (for/fold ((t t))
            ((opt (in-list opts)))
    (match-define (list kw trait) opt)
    (define handler (if (table? trait)
                        (or? (dict-ref trait :<setmeta>) identity)
                        trait))
    (let ((handled (handler t)))
      (unless (table? handled)
        (error '#%table "expected ~a trait to return table? got ~a" kw handled))
      handled)))


(define (table-maker t)
  (define-values (table-type _) (struct-info (if (table? t) t <table>)))
  (struct-type-make-constructor table-type))


;; TODO We allow extending table struct by defining new Racket structs that
;; inherit from table. We'd like the default constructor i.e. {} and therefore
;; #%table to work seemlessly with any such extended structs. To that purpose we
;; reflect constructor procedure from the metatable instance (see table-maker used
;; below). However, for this cute trick to work the derived structs must not
;; define any extra fields and they must be #:transparent so that the most
;; specific struct type maybe reflected. To make such extensions less brittle we
;; may need to provide a struct-like macro to limit user options. Alternatively,
;; user could supply a constructor procedure explicitly as a slot on the metatable
;; instance. Present implementation has a cute feature where inheritance just
;; works and any descendants of an extended struct are of that type e.g. if you
;; construct with table/evt, any subsequent metatables and their instances will be
;; table/evt? To achieve consistent metatable isa relations with constructor slot
;; idea such slot may need to be looked up on the metatable chain with get.


;;** - #%table --------------------------------------------------- *;;


(define-syntax (#%table stx)
  (syntax-parse stx
    ((_ <mt> ((kw trait) ...) (entry ...))
     (syntax/loc stx
       (let* ((h (ht entry ...))
              (make-table (table-maker <mt>))
              (t (make-table h <mt>))
              (metamethod (or? (meta-dict-ref t :<setmeta>) identity))
              (undefs (for/list (((k v) (in-mutable-hash h))
                                 #:when (undefined? v))
                        k)))
         (for-each (curry dict-remove! h) undefs)
         ;; TODO runtime error reporting here is not great - shows
         ;; full expansion in trace. Is there a way to show in terms
         ;; of actual expression i.e. table constructor? Case in
         ;; point when <spec> contract fails.
         (add-traits (metamethod t) (list (list 'kw trait) ...)))))))


;;** - table ----------------------------------------------------- *;;


(define-syntax-parser table-instance

  ((_ #:mt ~! mt:expr entry:table-entry ...)
   #:with #%table (datum->syntax this-syntax '#%table this-syntax)
   (syntax/loc this-syntax
     (let ((<mt> mt))
       (unless (table? <mt>) (raise-argument-error 'table "table?" <mt>))
       (#%table <mt> () (entry ...)))))

  ((_ entry:table-entry ...)
   (syntax/loc this-syntax
     (table-instance #:mt <table> entry ...))))


;;** - {} -------------------------------------------------------- *;;


;; TODO would it make sense to use <table> binding at the call site? Thereby
;; allowing the user to swap it for something else? Beware accidentally making
;; <table> dynamically scoped though? I think the same trick as with #%table would
;; work here.

(begin-for-syntax

  (define (parse-table-constructor stx)
    (syntax-parse stx
      #:context (list '|{}| (with-syntax (((_ e ...) stx))
                              ;; doesn't seem to effect paren shape in error msg
                              (syntax-property (syntax/loc stx {e ...})
                                               'paren-shape #\{)))
      ((_ (~optional (~seq mt:id) #:defaults ((mt #'<table>)))
          trait:option ...
          entry:table-entry ...)
       #:with #%table (datum->syntax stx '#%table stx)
       (syntax/loc stx
         ;; (#%table <mt> ((keyword trait) ...) ((key val) ...))
         (cond
           ((table? mt) (#%table mt ((trait.kw trait.opt) ...) (entry ...)))
           ((procedure? mt) (mt (#%table <table> ((trait.kw trait.opt) ...) (entry ...))))
           (else (raise-argument-error '|{}| "table? or procedure?" mt))))))))


;;* #%app -------------------------------------------------------- *;;


(define : (make-keyword-procedure
           (λ (kws kw-args table key . rest)
             (keyword-apply (get table key) kws kw-args rest))
           (λ (table key . rest) (apply (get table key) rest))))


(define :: (make-keyword-procedure
            (λ (kws kw-args table key . rest)
              (keyword-apply (get table key) kws kw-args table rest))
            (λ (table key . rest) (apply (get table key) table rest))))


(define-syntax (#%app stx)
  (cond
    ((eq? #\{ (syntax-property stx 'paren-shape))
     ;; {} => delegate to #%table constructor
     (parse-table-constructor stx))

    (else
     ;; TODO by the time we get to #%app no unbound identifier will have been
     ;; wrapped in #%top, so we cannot reliably tell if identifier in the app
     ;; position is in fact unbound. We therefore perform unbound? check manually
     ;; (with our own free-id syntax-class). Alternatively, we could force
     ;; expansion with local-expand. What's the right way to handle this?
     (syntax-parse stx
       ((_ (~and app:tag _:free-id) ~! table arg ...)
        ;; (:key table . args) =>
        (syntax/loc stx ((get table app) arg ...)))

       ((_ (~and app:method _:free-id) ~! table arg ...)
        ;; (::key table . args) =>
        #:with tag (method->tag #'app)
        (syntax/loc stx (let ((t table)) ((get t tag) t arg ...))))

       (_
        ;; => delegate to Racket's #%app
        (with-syntax (((_ . rest) stx))
          (syntax/loc stx (racket/#%app . rest))))))))


(module+ test
  (define/checked <c> {(:<setmeta> (λ (t) (set t :answer 42)))})

  (test-case "table constructors"
    (check-equal? (table-instance) {})
    (check-equal? (table-instance (:a 1)) {(:a 1)})
    (check-equal? (table-instance #:mt <c> (:a 1)) {<c> (:a 1)})
    ;; set-meta
    (check-eq? (dict-ref (set-meta {} <c>) :answer) 42))

  (test-case "undefined values"
    (define t {(:a 1) (:b 2)})
    (check-equal? {(:a 1) (:c undefined) (:b 2) (:d undefined)} t)
    (check-equal? (set t :c undefined) t)
    (check-equal? (set t :b undefined) {(:a 1)})
    (check-equal? (rm t :a) {}))

  (test-case "Default table constructor invokes <setmeta>"
    (define/checked c {<c> (:a 1)})
    (check-eq? (get c :a) 1)
    (check-eq? (get c :answer) 42)
    (check-eq? (dict-ref c :answer) 42))

  (test-case "Use #%table from macro invocation context"
    (let-syntax ([#%table (syntax-rules () [(_ mt (trait ...) (entry ...)) (ht entry ...)])])
      (check-equal? (ht (:a 1)) {(:a 1)})))

  (test-case ": and :: syntax in app position"
    (define/checked tb {(:a 1)
                        (:b 2)
                        (:meth (λ (self . keys) (for/list ((k keys)) (get self k))))
                        (:kwmeth (λ (self #:key k) (get self k)))
                        (:bound (const 42))})
    (check-equal? (:meth tb tb :a) '(1))
    (check-equal? (: tb :meth tb :a) '(1))

    (check-equal? (::meth tb :a) '(1))
    (check-equal? (:: tb :meth :a) '(1))

    (check-equal? (apply : tb :meth tb '(:a :b)) '(1 2))
    (check-equal? (apply :: tb :meth '(:a :b)) '(1 2))

    (check-eq? (::kwmeth tb #:key :a) 1)
    (check-eq? (:: tb :kwmeth #:key :a) 1)
    (check-eq? (keyword-apply : '(#:key) '(:a) tb :kwmeth (list tb)) 1)
    (check-eq? (keyword-apply :: '(#:key) '(:a) tb :kwmeth '()) 1)
    (check-eq? (keyword-apply :: #:key :a '() '() tb :kwmeth '()) 1)

    (check-exn exn? (thunk (define :bound 42) (:bound tb)) "application: not a procedure")
    (check-exn exn? (thunk (define :bound 42) (: tb :bound)) "application: not a procedure")
    ;; but
    (check-eq? (let ((:bound 42)) (::bound tb)) 42)))


;;* <spec> ------------------------------------------------------- *;;


;; TODO better error reports needed: k, v, predicate that failed. I bet contracts
;; RHS should be able to capture which subcontract failed exactly, but I dunno
;; how that works. Ditto contract error reporting facilities.

(define <spec>
  {(:open (case-lambda
            ((spec t)
             (for (((k pred?) (in-dict spec)))
               ;; TODO should this be get instead of dict-ref?
               (unless (pred? (dict-ref t k))
                 (error '#%table "slot ~a violated its contract" k)))
             t)
            ((spec t k v)
             (define pred? (or? (dict-ref spec k) (const #t)))
             (unless (pred? v)
               (error 'set "slot ~a violated its contract" k))
             t)))
   (:closed (case-lambda
              ((spec t)
               (define slots (list->mutable-seteq (dict-keys t)))
               (for (((k pred?) (in-dict spec)))
                 (unless (pred? (dict-ref t k))
                   (error '#%table "slot ~a violated its contract" k))
                 (set-remove! slots k))
               (unless (set-empty? slots)
                 (error '#%table "slots ~a not allowed by <spec>" (set->list slots)))
               t)
              ((spec t k v)
               (define pred? (or? (dict-ref spec k)
                                  (const (error 'set "slot ~a not allowed by <spec>" k))))
               (unless (pred? v)
                 (error 'set "slot ~a violated its contract" k))
               t)))
   (:setmeta (λ (spec)
               (set spec :<setmeta>
                    (λ (mt)
                      ;; remove :<setmeta> slot from :check table - ugly
                      (rm spec :<setmeta>)
                      (set mt :check spec)
                      (set mt :<setmeta> (λ (t) (t::check)))
                      (set mt :<set> (λ (t k v) (t::check k v) (dict-set! t k v) t))
                      mt))))})


(define <open> {<spec> (:<proc> <spec>:open)
                       (:<setmeta> <spec>:setmeta)})


(define <closed> {<spec> (:<proc> <spec>:closed)
                         (:<setmeta> <spec>:setmeta)})


(module+ test

  (test-case "<open>"
    (define/checked <mt> {#:check {<open> (:a (or/c undefined? natural?))
                                          (:b (or/c undefined? symbol?))
                                          (:c symbol?)}})
    (define/checked t {<mt> (:a 1) (:c 'c)})
    ;; :c must be present
    (check-exn exn? (thunk {<mt>}) "slot :c violated its contract")
    ;; :c and :b must be symbols
    (check-exn exn? (thunk {<mt> (:c 42)}) "slot :c violated its contract")
    (check-exn exn? (thunk (set t :c 42))  "slot :c violated its contract")
    (check-exn exn? (thunk (set t :b 42))  "slot :c violated its contract")
    ;; happy path
    (check-eq? t:c 'c)
    (check-eq? (get (set t :b 'b) :b) 'b))


  (test-case "<closed>"
    (define/checked <mt> {#:check {<closed> (:a (or/c undefined? natural?))
                                            (:b (or/c undefined? symbol?))
                                            (:c symbol?)}})
    (define/checked t {<mt> (:a 1) (:c 'c)})
    ;; only speced slots allowed
    (check-exn exn? (thunk {<mt> (:a 1) (:d 4)}) "slots (:d) not allowed")
    (check-exn exn? (thunk (set t :d 4)) "slot :d not allowed")
    ;; otherwise like <spec>
    (check-exn exn? (thunk {<mt>}) "slot :c violated its contract")
    (check-exn exn? (thunk {<mt> (:c 42)}) "slot :c violated its contract")
    (check-exn exn? (thunk (set t :c 42))  "slot :c violated its contract")
    (check-exn exn? (thunk (set t :b 42))  "slot :c violated its contract")
    (check-eq? t:c 'c)
    (check-eq? (get (set t :b 'b) :b) 'b)))


;;** - spec combinators ------------------------------------------ *;;


(define (required . c) (apply and/c (compose not undefined?) c))
(define (optional . c)
  (define contract (if (empty? c) (list any/c) c))
  (apply or/c undefined? contract))


(define-syntax-parser req
  ((_ c:expr ...) (syntax/loc this-syntax (required c ...)))
  (_:id (syntax/loc this-syntax (required))))


(define-syntax-parser opt
  ((_ c:expr ...) (syntax/loc this-syntax (optional c ...)))
  (_:id (syntax/loc this-syntax (optional))))


(module+ test
  (test-case "opt and req contract combinators"
    (define/checked string-or-num! (required (or/c string? number?)))
    (define/checked string-or-num? (optional (or/c string? number?)))
    (check-true (string-or-num! 42))
    (check-true (string-or-num! ""))
    (check-false (string-or-num! undefined))
    (check-true (string-or-num? undefined))
    (check-false (string-or-num? 's))
    (check-false ((req) undefined))
    (check-true ((opt) undefined))
    (check-true ((opt) 42))

    (define/checked <mt> {#:check {<open> (:? (opt (or/c string? symbol?)))
                                          (:! (req number?))}})
    (check-exn exn? (thunk {<mt>}) "slot :! violated its contract")
    (check-exn exn? (thunk {<mt> (:! 1) (:? 2)}) "slot :? violated its contract")
    (check-eq? (get {<mt> (:! 42)} :!) 42)

    (define/checked <mtt> {#:check {<open> (:? opt)
                                           (:! req)}})
    (check-exn exn? (thunk {<mtt>}) "slot :! violated its contract")
    (check-eq? (get {<mtt> (:! '!)} :!) '!)
    (check-eq? (get {<mtt> (:! '!) (:? '?)} :?) '?)))


;;* define ------------------------------------------------------- *;;


(begin-for-syntax

  (require syntax/define)

  (define (λ/self λ self)
    (syntax-parse λ
      ((_ rest:id body ...)
       #:with self self
       (syntax/loc λ (lambda (self . rest) body ...)))

      ((_ (arg ...) body ...)
       #:with self self
       (syntax/loc λ (lambda (self arg ...) body ...))))))


;; TODO Unless I screwed up define/table should be a drop-in replacement for
;; Racket's define. So #lang racket/tables should provide rename-out as define.
(define-syntax (define/table stx)

  (syntax-parse stx
    ((_ (~var id (table-sep-key "::")) rhs:expr)
     ;; (define t::k val) =>
     (syntax/loc stx
       (begin
         (define t::k rhs)
         (void (set id.table 'id.tag t::k)))))

    ((_ (~var id (table-sep-key ":")) rhs:expr)
     ;; (define t:k val) =>
     (syntax/loc stx
       (begin
         (define t:k rhs)
         (void (set id.table 'id.tag t:k)))))

    ((_ id:id rhs:expr)
     ;; (define id val) =>
     (syntax/loc stx (define id rhs)))

    (_
     ;; (define (t::k ...) body)
     ;; (define (t:k ...) body)
     ;; (define (id ...) body)
     ;; =>
     (let-values (((id rhs) (normalize-definition stx #'lambda #t #t)))
       (cond
         ((table-sep-key? id "::")
          (with-syntax ((λ (λ/self rhs (datum->syntax id 'self)))
                        (id id))
            (syntax/loc stx (define/table id λ))))

         ((table-sep-key? id ":")
          (with-syntax ((λ rhs)
                        (id id))
            (syntax/loc stx (define/table id λ))))

         (else
          (with-syntax ((λ rhs)
                        (id id))
            (syntax/loc stx (define id λ)))))))))


(module+ test
  (test-case "define/table"
    (define t {})
    (checked (define/table t:a 1))
    (checked (define/table t:b 2))
    (checked (define/table (t:foo a) a))
    (check-eq? (t:foo 1) 1)
    (checked (define/table ((t:bar a) b) (+ a b)))
    (check-eq? ((t:bar 1) 2) 3)
    (checked (define/table (t:baz a #:b (b 2)) (+ a b)))
    (check-eq? (t:baz 1) 3)
    (check-eq? (t:baz 1 #:b 0) 1)
    (checked (define/table (t::get k) (get self k)))
    (check-eq? (t::get :a) 1)
    (checked (define/table ((t::get+ k1) k2) (+ (self::get k1) (self::get k2))))
    (check-eq? ((t::get+ :a) :b) 3)
    (checked (define/table (t::get* . keys) (apply + (map (curry get self) keys))))
    (check-eq? (t::get* :a :b) 3)
    (define/table a 1)
    (check-eq? a 1)))


;;* <table/evt> -------------------------------------------------- *;;


(struct table/evt table ()
  ;; NOTE must be #:transparent with current implementation of #:table that relies
  ;; on reflection to get the most specific struct type
  #:transparent
  #:property prop:evt (λ (t)
                        (define evt (get t :evt))
                        (cond
                          ((evt? evt) evt)
                          ((procedure? evt) (evt t)))))


(define <table/evt> (table/evt (ht) <table>))


(module+ test
  (test-case "<table/evt>"
    (define/checked evt {<table/evt> (:a 1) (:evt (open-input-string "42"))})
    (check-true (table? evt))
    (check-true (table/evt? evt))
    (check-eq? (read (sync evt)) 42)
    ;; gen:dict should be inherited from table
    (check-eq? (dict-ref evt :a) 1)
    (check-eq? (get evt :a) 1)))


;;* <tables> ----------------------------------------------------- *;;


(define <tables> {})


(define/table (<tables>::<isa?> mt)
  (define tables self)
  (for/or ((t (in-dict-values tables)))
    (or (eq? t mt)
        (isa? t mt))))


(define/table (<tables>::<get> k)
  ;; TODO for now order is induced by symbolic keys, at least until we start using
  ;; insertion ordered hash-maps for table contents. Alternative would be to store
  ;; parent tables in a list under e.g. :tables
  (define tables (map (curry get self) (sort (dict-keys self) symbol<?)))
  ;; TODO implement ormap? for/or? for/first?
  (or (for/or ((t (in-list tables)))
        (let ((v (get t k)))
          (or? v #f)))
      (get (table-meta self) k)
      undefined))


(module+ test
  (test-case "<tables>"
    (define/checked <mt1> {(:do-1 (λ (t) t:a))
                           (:do (λ (t) (t::do-1)))})

    (define/checked <mt2> {(:do-2 (λ (t) t:b))
                           (:do (λ (t) (t::do-2)))})


    (define/checked <mts> {<tables> (:mt1 <mt1>)
                                    (:mt2 <mt2>)})

    (define/checked ts {<mts> (:a 1) (:b 2)})
    (check-eq? (ts::do) 1)
    (check-eq? (ts::do-1) 1)
    (check-eq? (ts::do-2) 2)
    (check-true (isa? ts <tables>))
    (check-true (isa? ts <mts>))
    (check-true (isa? ts <mt1>))
    (check-true (isa? ts <mt2>))
    (check-true (isa? ts <table>))))
