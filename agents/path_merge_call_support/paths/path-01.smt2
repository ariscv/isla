; 从实测迹转换；输入名归一化，枚举及寄存器事件保存在原始迹中。
; 返回值保留符号表达式；get-value 的模型值不代表恒定返回值。
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const pte_flags (_ BitVec 8))
(declare-const pte_ext (_ BitVec 10))
(define-fun v0 () (_ BitVec 8) pte_flags)
(define-fun v1 () (_ BitVec 1) ((_ extract 0 0) v0))
(define-fun v2 () Bool (= v1 #b0))
(define-fun path_condition () Bool (and v2))
(define-fun result () Bool true)
(assert path_condition)
(check-sat)
(get-value (result))
