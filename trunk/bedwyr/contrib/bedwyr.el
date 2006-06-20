;; Emacs mode for Bedwyr definition files.
;;
;; Based on tutorial at:
;;   http://two-wugs.net/emacs/mode-tutorial.html
;;

(defvar bedwyr-mode-hook nil)

(defvar bedwyr-program nil)

(defun bedwyr-run (&optional cmd)
  "Run Bedwyr on the current file"
  (interactive)
  (switch-to-buffer "*bedwyr*")
  (kill-buffer "*bedwyr*")
  (if cmd
      (setq bedwyr-program cmd)
    (if (not bedwyr-program)
        (setq bedwyr-program
              (read-from-minibuffer "Bedwyr program to run: " "bedwyr"))))
  (switch-to-buffer (make-comint "bedwyr" bedwyr-program nil (buffer-file-name))))

(defvar bedwyr-mode-map
  (let ((map (make-keymap)))
    (define-key map "\C-c\C-c" 'bedwyr-run)
    map)
  "Keymap for Bedwyr major mode")

(add-to-list 'auto-mode-alist '("\\.def\\'" . bedwyr-mode))

(defun make-regex (&rest args)
  (concat "\\<" (regexp-opt args) "\\>"))

(defvar bedwyr-font-lock-keywords
  (list
   (cons (make-regex "false" "true") font-lock-constant-face)
   (cons (make-regex "pi" "sigma" "nabla") font-lock-keyword-face)
   (cons (make-regex "inductive" "coinductive") font-lock-keyword-face)
   (cons (make-regex "print") font-lock-keyword-face)
   (cons "\\#table" font-lock-keyword-face)
   (cons "\\#show_table" font-lock-keyword-face)
   (cons "\\<[A-Z][A-Za-z0-9'/]*" font-lock-variable-name-face))
  "Default highlighting for Bedwyr mode")

(defun bedwyr-indent-line ()
  "Indent current line as Bedwyr code"
  (interactive)
  (beginning-of-line)
  (let (cur-indent)
    (save-excursion
      (while (null cur-indent)
        (forward-line -1)
        (cond
         ((bobp) (setq cur-indent 0))
         ((looking-at "^%"))
         ((looking-at "^\\W*$"))
         ((looking-at "^.*\\.\\W*$") (setq cur-indent 0))
         ((looking-at "^.*:=") (setq cur-indent default-tab-width))
         (t (if (> (current-indentation) 0)
                (setq cur-indent (current-indentation))
              (progn
                (let ((start (point)))
                  (forward-word 1)
                  (setq cur-indent (1+ (- (point) start))))))))))
    (indent-line-to cur-indent)))

(defvar bedwyr-mode-syntax-table
  (let ((bedwyr-mode-syntax-table (make-syntax-table)))
    (modify-syntax-entry ?_ "w" bedwyr-mode-syntax-table)
    (modify-syntax-entry ?' "w" bedwyr-mode-syntax-table)
    (modify-syntax-entry ?/ "w" bedwyr-mode-syntax-table)
    (modify-syntax-entry ?% "<" bedwyr-mode-syntax-table)
    (modify-syntax-entry ?\n ">" bedwyr-mode-syntax-table)
    (modify-syntax-entry ?. "." bedwyr-mode-syntax-table)
    (modify-syntax-entry ?+ "." bedwyr-mode-syntax-table)
    (modify-syntax-entry ?- "." bedwyr-mode-syntax-table)
    (modify-syntax-entry ?* "." bedwyr-mode-syntax-table)
    (modify-syntax-entry ?= "." bedwyr-mode-syntax-table)
    (modify-syntax-entry ?> "." bedwyr-mode-syntax-table)
    (modify-syntax-entry ?< "." bedwyr-mode-syntax-table)
    (modify-syntax-entry ?# "." bedwyr-mode-syntax-table)
    (modify-syntax-entry ?\ "." bedwyr-mode-syntax-table)
    bedwyr-mode-syntax-table)
  "Syntax table for bedwyr-mode")

(defun bedwyr-mode ()
  "Mjaor mode for editing Bedwyr definition files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table bedwyr-mode-syntax-table)
  (use-local-map bedwyr-mode-map)
  (set (make-local-variable 'font-lock-defaults)
       '(bedwyr-font-lock-keywords))
  (set (make-local-variable 'indent-line-function) 'bedwyr-indent-line)
  (setq major-mode 'bedwyr-mode)
  (setq mode-name "Bedwyr")
  (run-hooks 'bedwyr-mode-hook))

(provide 'bedwyr-mode)
