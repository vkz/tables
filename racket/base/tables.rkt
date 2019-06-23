#lang racket/base

(require tables)
(provide (rename-out [table-#%top #%top] [table-#%app #%app])
         (except-out (all-from-out tables) table-#%top table-#%app)
         (except-out (all-from-out racket/base) #%top #%app))

(module reader syntax/module-reader
  racket/base/tables)
