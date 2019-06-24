#lang racket/base

(require tables)
(provide (except-out (all-from-out racket/base) #%top #%app)
         (all-from-out tables)
         (rename-out [table-#%top #%top] [table-#%app #%app]))


(module reader syntax/module-reader
  racket/base/tables)
