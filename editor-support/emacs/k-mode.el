;;; k-mode.el -- Emacs mode for the K Framework

;; Currently has syntax highlighting for:
;;  - keywords
;;  - declarations (e.g. ops, syntax, etc)
;;  - Quoted identifiers (e.g. for terminals in the syntax)
;; Also has a menu and compilation through C-c C-c


;; Author: Michael Ilseman

;; Usage: add the below to your .emacs file:
;;     (setq load-path (cons "path/to/this/file" load-path))
;;     (load-library "k-mode")
;;     (add-to-list 'auto-mode-alist '("\\.k$" . k-mode)) ;; to launch k-mode for .k files
(require 'comint)

;;;; Options ;;;;
(defvar k-dash-comments nil
  "Set to make \"--\" be used as a beginning of a line comment
   (emacs's syntax table is unable to differentiate 3 character long comment beginners)"
)
(defvar k-path "~/k-framework"
  "Path to the k-framework. Set if you wish to use kompile from emacs. Defaults to ~/k-framework.
   Currently doesn't do anything."
)

;;;; Syntax Highlighting ;;;;
(setq k-keywords
      '("syntax" "kmod" "endkm" "including" ; "::=" "|"
        "sort" "op" "subsort" "rule" "eq" "ceq" "load")
      k-syntax-terminals-regex
      "`\\w+"
      k-declarations ;; Syntax highlight the name after a declaration
      "\\(syntax\\|sort\\|op\\) \\([a-zA-Z{}\\-]+\\)"
)

;; Set up the regexes
(setq k-keywords-regex
      (regexp-opt k-keywords 'words)
)

;; Put them all together
(setq k-font-lock-keywords
      `((,k-declarations 2 font-lock-builtin-face)
        (,k-keywords-regex . font-lock-keyword-face)
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
  (if k-dash-comments (modify-syntax-entry ?- ". 1b2b" k-mode-syntax-table))
)


;;;; K Bindings and menu ;;;;
(defvar k-prev-load-file nil
  "Record the last directory and file used in loading or compiling"
)
(defcustom k-source-modes '(k-mode)
  "Determine if a buffer represents a k file"
)
;; (defun k-mode-kompile (cmd)
;;   ;; (interactive (comint-get-source "Kompile k file: " k-prev-load-file k-source-modes nil))
;;   ;; (comint-check-source file-name) ; check to see if buffer has been modified and not saved
;;   ;; (setq k-prev-load-file (cons (file-name-directory file-name)
;;   ;;                              (file-name-nondirectory file-name)))
;;   ;; ;; (comint-send-string (inferior-lisp-proc)
;; 	;; ;; 	      (format inferior-lisp-load-command file-name))
;;   ;; ;; (switch-to-lisp t))
;;   ;; (message file-name)
;;   ;; (setq kompile-buffer (make-comint "Kompile" "zsh" nil))
;;   ;; (comint-send-string kompile-buffer "cd" nil (file-name-directory file-name))
;;   ;; (comint-send-string kompile-buffer "~/k-framework/tools/kompile.pl" nil (file-name-nondirectory file-name))
;;   (interactive "scmd")
;;   (compile cmd)
;;   nil
;; )
(defun k-mode-about ()
  (interactive)
  (message "k-mode for the K Framework")
)

(defun setup-k-mode-map ()
  (setq k-mode-map (make-sparse-keymap))

  ;; Keyboard shortcuts
  (define-key k-mode-map (kbd "C-c C-c") 'compile)

  ;; Define the menu
  (define-key k-mode-map [menu-bar] (make-sparse-keymap))

  (let ((menuMap (make-sparse-keymap "K Framework")))
    (define-key k-mode-map [menu-bar k] (cons "K Framework" menuMap))
    (define-key menuMap [about]
      '("About k-mode" . k-mode-about))
    ;; (define-key menuMap [customize]
    ;;   '("Customize k-mode" . k-customize))
    (define-key menuMap [separator]
      '("--"))
    (define-key menuMap [kompile]
      '("kompile" . compile)))
)





;;;; K Mode ;;;;

(define-derived-mode k-mode fundamental-mode
  "k mode"
  "Major Mode for the K framwork"
  (setq font-lock-defaults '((k-font-lock-keywords)))

  ;; Comment entries
  (set-comment-highlighting)

  ;; Shortcuts and menu
  (setup-k-mode-map)
  (use-local-map k-mode-map)

  ;; Clear up memory
  ;;(setq k-keywords nil k-keywords-regex nil)
)

(provide 'k-mode)
