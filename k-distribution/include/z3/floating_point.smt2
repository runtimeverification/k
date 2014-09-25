; dummy prelude for floating-point because the set-logic command is not
; supported when using the API parseSmtlib2String
; see http://stackoverflow.com/a/7349729

; YilongL: hack to avoid Z3 parser error when translating smtlib expression
; the problem is that kernelc.k imports list_pattern but QF_FPA doesn't work
; with Array yet
(declare-sort IntSet)
