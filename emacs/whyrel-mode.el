(setq whyrel-keywords
      '("meth" "requires" "ensures" "effects" "reads" "writes" "reads/writes"
        "inductive" "predicate" "lemma" "axiom" "boundary" "ghost" "datagroup"
        "class" "interface" "module" "bimodule" "end" "if" "else" "while"
        "do" "done" "public" "modscope" "let" "forall" "exists" "and" "or" "not"
        "private" "coupling" "in" "havoc"
        "skip" "new" "var" "assume" "assert" "invariant" "variant"
        "Havoc" "Var" "While" "WhileL" "WhileR" "If"
        "If4" "thenThen" "thenElse" "elseThen" "elseElse"
        "rd" "wr" "rw" "import" "theory" "as" "contains" "then" "Connect"
        "Link" "Assume" "Assert" "with" "extern" "type" "const" "default"))

(setq whyrel-left-pairs '("<|" "<]" "[<" "|_"))

(setq whyrel-right-pairs '("|>" "[>" ">]" "_|"))

(setq whyrel-default-functions '("Agree" "Both" "Type" "old"))

(setq whyrel-default-types '("int" "array" "bool"))

(setq whyrel-constants '("null" "True" "False" "true" "false"))

(setq whyrel-font-lock-keywords
      (let ((whyrel-keywords-regexp (regexp-opt whyrel-keywords 'symbols))
            (whyrel-left-pairs-regexp (regexp-opt whyrel-left-pairs 'string))
            (whyrel-right-pairs-regexp (regexp-opt whyrel-right-pairs 'string))
            (whyrel-default-types-regexp
             (regexp-opt whyrel-default-types 'symbols))
            (whyrel-types-regexp "\\:\\s *\\([a-zA-Z][_a-zA-Z0-9'+]*\\)")
            (whyrel-constants-regexp (regexp-opt whyrel-constants 'symbols))
            (whyrel-cast-regexp
             (concat
              "\\([a-zA-Z][_a-zA-Z0-9']*\\)\\s *"
              "\\:\\s *\\([a-zA-Z][_a-zA-Z0-9'+]*\\)"))
            (whyrel-in-region-regexp "\\:.*?\\(\\b\\in\\b\\).*?.")
            (whyrel-let-name-regexp "let\\s +\\([a-zA-Z][_a-zA-Z0-9']*\\)")
            (whyrel-let-in-regexp "let\\s +.*?\\s *=.*?\\(in\\)")
            (whyrel-bilet-name-regexp
             (concat "let.*?\\s +\\([a-zA-Z][_a-zA-Z0-9']*\\)\\s *|"
                     "\\s *\\([a-zA-Z][_a-zA-Z0-9']*\\)"))
            (whyrel-var-name-regexp "var\\s +\\([a-zA-Z][_a-zA-Z0-9']*\\)")
            ;; (whyrel-var-in-regexp
            ;;  (concat "var.*?\\s +\\([a-zA-Z][_a-zA-Z0-9']*\\)"
            ;;          "\\s *:\\s *.*?\\s +\\(\\bin\\b\\)"))
            (whyrel-function-regexp
             (concat "\\(meth\\|predicate\\|lemma\\|axiom\\)"
                     "\\s +\\([a-zA-Z][_a-zA-Z0-9']*\\)"))
            (whyrel-class-regexp "class\\s *\\([a-zA-Z][_a-zA-Z0-9']*\\)")
            (whyrel-type-pred-regexp "Type(.*,\\s *\\(\\b.*\\b\\)")
            (whyrel-module-regexp
             (concat
              "module\\s +\\(\\b[a-zA-Z0-9_']+\\b\\)\\s *:\\s *"
              "\\(\\b[a-zA-Z0-9_']+\\b\\)\\s *=$"))
            (whyrel-default-functions-regexp
             (regexp-opt whyrel-default-functions 'symbols))
            (whyrel-extern-type-regexp
             "extern type \\(\\b[a-zA-Z0-9']+\\b\\)")
            (whyrel-extern-function-regexp
             "extern \\(\\b[a-zA-Z0-9']+\\b\\)"))
        `((,whyrel-keywords-regexp . font-lock-keyword-face)
          (,whyrel-left-pairs-regexp . font-lock-doc-face)
          (,whyrel-right-pairs-regexp . font-lock-doc-face)
          (,whyrel-cast-regexp (1 font-lock-variable-name-face))
          (,whyrel-default-types-regexp (1 font-lock-type-face))
          (,whyrel-types-regexp (1 font-lock-type-face))
          (,whyrel-let-name-regexp (1 font-lock-variable-name-face))
          (,whyrel-let-in-regexp (1 font-lock-keyword-face))
          (,whyrel-bilet-name-regexp (2 font-lock-variable-name-face))
          (,whyrel-var-name-regexp (1 font-lock-variable-name-face))
          ;; (,whyrel-var-in-regexp (2 font-lock-keyword-face))
          (,whyrel-in-region-regexp (1 font-lock-keyword-face))
          (,whyrel-function-regexp (2 font-lock-function-name-face))
          (,whyrel-class-regexp (1 font-lock-type-face))
          (,whyrel-default-functions-regexp . font-lock-builtin-face)
          (,whyrel-constants-regexp . font-lock-constant-face)
          (,whyrel-type-pred-regexp (1 font-lock-type-face))
          (,whyrel-extern-type-regexp (1 font-lock-type-face))
          (,whyrel-extern-function-regexp (1 font-lock-function-name-face))
          (,whyrel-module-regexp . (1 default))
          (,whyrel-module-regexp . (2 default))
          ("extern\\s +.*?\\s *("
           ("[, \t]*\\(\\b[a-zA-Z_]+\\b\\)"
            nil
            nil
            (1 font-lock-type-face))))))

(defvar whyrel-mode-syntax-table nil "Syntax table for `whyrel-mode'.")
(setq whyrel-mode-syntax-table
      (let ((syn-table (make-syntax-table)))
        ;; comments
        (modify-syntax-entry ?\/ ". 14" syn-table)
        (modify-syntax-entry ?* ". 23" syn-table)
        syn-table))

(defvar whyrel-mode-map nil "Keymap for `whyrel-mode'.")
(setq whyrel-mode-map (make-sparse-keymap))

(define-derived-mode whyrel-mode prog-mode "WhyRel"
  "Major mode for editing WhyRel programs"
  (setq font-lock-defaults '((whyrel-font-lock-keywords)))
  (setq-local indent-tabs-mode nil)
  (setq-local tab-width 2)
  (setq-local comment-start "/*")
  (setq-local comment-end "*/")

  (setq-local prettify-symbols-alist
              '((">=" . ?≥)
                ("<=" . ?≤)
                ("->" . ?→)
                ("/\\" . ?∧)
                ("\\/" . ?∨)
                ("forall" . ?∀)
                ("exists" . ?∃)
                ("<>" . ?≠)))
  (prettify-symbols-mode 1)
  )

(provide 'whyrel-mode)
