(ns player.macros)

(defmacro soft-assert [condition & msg]
  `(when-not ~condition
     (.warn js/console "Soft assertion failed:" ~(str condition) ~@msg)))