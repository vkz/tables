#lang racket

(require tables)
(provide (except-out (all-from-out racket) #%top #%app)
         (all-from-out tables)
         (rename-out [table-#%top #%top] [table-#%app #%app]))

(module reader syntax/module-reader
  racket/tables)
