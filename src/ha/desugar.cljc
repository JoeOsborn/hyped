(ns ha.desugar
  (:require
    [ha.ha :as ha]))

; Desugars HAs with bounded acceleration, transition priorities, required transitions, and disjunctive guards into ones without all that stuff.

(defn bounded-acc-to-states [has]
  has)

(defn priorities-to-disjoint-guards [has]
  has)

(defn required-transitions-to-invariants [has]
  has)

(defn invariant-disjunctions-to-states [has]
  has)

(defn guard-disjunctions-to-transitions [has]
  has)

(defn desugar [has]
  (-> has
      (bounded-acc-to-states)
      (priorities-to-disjoint-guards)
      (required-transitions-to-invariants)
      (invariant-disjunctions-to-states)
      (guard-disjunctions-to-transitions)))