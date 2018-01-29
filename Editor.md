Here we collect some information on how to set up your editor to properly input
and output the unicode characters used throughout Iris.

## General: Unicode Fonts

Most editors will just use system fonts for rendering unicode characters and do
not need furhter configuration once the fonts are installed.  Here are some
combinations of fonts that are known to give readable results (i.e., each of
these sets of fonts covers all the required characters):

* Fira Mono, DejaVu Mono, Symbola

## Emacs

### Unicode Input

First, install `math-symbol-lists` by doing `M-x package-install math-symbol-lists`.

Next, add the following to your `~/.emacs` to configure an input method based on the math symbol list, and with some custom aliases for symbols used a lot in Iris:
```
;; Input of unicode symbols
(require 'math-symbol-lists)
; Automatically use math input method for Coq files
(add-hook 'coq-mode-hook (lambda () (set-input-method "math")))
; Input method for the minibuffer
(defun my-inherit-input-method ()
  "Inherit input method from `minibuffer-selected-window'."
  (let* ((win (minibuffer-selected-window))
         (buf (and win (window-buffer win))))
    (when buf
      (activate-input-method (buffer-local-value 'current-input-method buf)))))
(add-hook 'minibuffer-setup-hook #'my-inherit-input-method)
; Define the actual input method
(quail-define-package "math" "UTF-8" "Ω" t)
(quail-define-rules ; add whatever extra rules you want to define here...
 ("\\mult"   ?⋅)
 ("\\ent"    ?⊢)
 ("\\valid"  ?✓)
 ("\\box"    ?□)
 ("\\later"  ?▷)
 ("\\pred"   ?φ)
 ("\\and"    ?∧)
 ("\\or"     ?∨)
 ("\\comp"   ?∘)
 ("\\ccomp"  ?◎)
 ("\\all"    ?∀)
 ("\\ex"     ?∃)
 ("\\to"     ?→)
 ("\\sep"    ?∗)
 ("\\lc"     ?⌜)
 ("\\rc"     ?⌝)
 ("\\lam"    ?λ)
 ("\\empty"  ?∅)
 ("\\Lam"    ?Λ)
 ("\\Sig"    ?Σ)
 ("\\-"      ?∖)
 ("\\aa"     ?●)
 ("\\af"     ?◯)
 ("\\iff"    ?↔)
 ("\\gname"  ?γ)
 ("\\incl"   ?≼)
 ("\\latert" ?▶)
)
(mapc (lambda (x)
        (if (cddr x)
            (quail-defrule (cadr x) (car (cddr x)))))
      (append math-symbol-list-basic math-symbol-list-extended))
```

### Font Configuration

Even when usable fonts are installed, Emacs tends to pick bad fonts for some
symbols like universal and existential quantifiers.  The following configuration
results in a decent choice for the symbols used in Iris:

```
;; Fonts
(set-face-attribute 'default nil :height 110) ; height is in 1/10pt
(dolist (ft (fontset-list))
  ; Main font
  (set-fontset-font ft 'unicode (font-spec :name "Monospace"))
  ; Fallback font
  ; Appending to the 'unicode list makes emacs unbearably slow.
  ;(set-fontset-font ft 'unicode (font-spec :name "DejaVu Sans Mono") nil 'append)
  (set-fontset-font ft nil (font-spec :name "DejaVu Sans Mono"))
)
; Fallback-fallback font
; If we 'append this to all fontsets, it picks Symbola even for some cases where DejaVu could
; be used. Adding it only to the "t" table makes it Do The Right Thing (TM).
(set-fontset-font t nil (font-spec :name "Symbola"))
```
