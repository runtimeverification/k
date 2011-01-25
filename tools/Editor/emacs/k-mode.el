;;; k-mode.el -- Emacs mode for the K Framework

;; Currently just has some trivial forms of synax highlighting

;; Author: Michael Ilseman



;;;; Syntax Highlighting ;;;;
(setq k-keywords
      '("syntax" "kmod" "endkm" "including" "::=" "|"
        "sort" "op" "subsort" "rule" "eq" "ceq")
      k-syntax-terminals-regex
      "`\\w+"
)

;; Set up the regexes
(setq k-keywords-regex
      (regexp-opt k-keywords 'words)
)

;; Put them all together
(setq k-font-lock-keywords
      `((,k-keywords-regex . font-lock-keyword-face)
        (,k-syntax-terminals-regex . font-lock-constant-face)
       )
)

;; Handle comments
(defun set-comment-highlighting ()
  "Set up comment highlighting"

  ;; comment style "// ..." and "/* ... */"
  (modify-syntax-entry ?\/ ". 124b" k-mode-syntax-table)
  (modify-syntax-entry ?\n "> b" k-mode-syntax-table)
  (modify-syntax-entry ?* ". 23" k-mode-syntax-table)

  ;; comment style "-- ..."
  (modify-syntax-entry ?- ". 1b2b" k-mode-syntax-table)
)


(define-derived-mode k-mode fundamental-mode
  "k mode"
  "Major Mode for the K framwork"
  (setq font-lock-defaults '((k-font-lock-keywords)))

  ;; Comment entries
  (set-comment-highlighting)

  ;; Clear up memory
  ;;(setq k-keywords nil k-keywords-regex nil)
)

