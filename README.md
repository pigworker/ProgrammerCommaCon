# Programmer
# ,
# Con

Using `.lagda.md` as a literate Agda format will be less frustrating
if you put

```elisp
(setq auto-mode-alist (cons '("\\.lagda.md$" . agda2-mode) auto-mode-alist))
```

in your `.emacs` file.
