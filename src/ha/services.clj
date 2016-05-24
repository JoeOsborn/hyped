(ns ha.services
  (:require [cognitect.transit :as transit]
            [ha.ha :as ha]
            [ha.rollout :as roll]
            [clojure.java.io :as jio]
            [clojure.string :as string]
            [ha.intervals :as iv]
            [ha.eval :as heval]
            [ha.z3 :as z3]
            [ha.desugar :as desugar])
  (:use [ring.middleware
         params
         keyword-params
         nested-params
         reload])
  (:import (java.io ByteArrayOutputStream)))

#_(defremote
    symx-1 [transit-args]
    (let [[ha-defs ha-vals] (transit/read (transit/reader transit-args
                                                          :json
                                                          (ha/transit-reader)))]
      (transit/write (ha/transit-writer nil) [])))

#_(def services (-> rpc/wrap-rpc
                    wrap-keyword-params
                    wrap-nested-params
                    wrap-params
                    ))

(def z3-lock 1)

(defn rpc-handler [req]
  (when (= (:uri req)
           "/rpc/explore")
    (println "req" req)
    (let [read-params (clojure.data.json/read (jio/reader (:body req)))
          read-method (get read-params "method")
          read-args (transit/read (ha/transit-reader (jio/input-stream (.getBytes (get read-params "arguments") "UTF-8"))))
          out-stream (ByteArrayOutputStream.)]
      (case read-method
        "symx-1"
        ; OK, let's do this. We want to know the one-step reachable regions, ie
        ; the reached pseudomodes of each successor state.
        (locking z3-lock
          (let [unroll-limit 5                              ; how many inert successor transitions do we reach forward to constrain t0?
                lookahead-time 1000
                [ha-defs ha-vals] read-args
                _ (assert (nil? ha.eval/guard-memo))
                z3 (z3/->z3 ha-defs {"proof" "false"
                                     "well_sorted_check" "true"
                                     "model" "true"
                                     "model_validate" "true"
                                     "unsat_core" "false"
                                     ;(ite_extra_rules, flat, elim_and, local_ctx, local_ctx_limit, blast_distinct, blast_distinct_threshold, som, som_blowup, hoist_mul, hoist_cmul, algebraic_number_evaluator, mul_to_power, expand_power, expand_tan, max_degree, eq2ineq, sort_sums, gcd_rounding, arith_lhs, elim_to_real, push_to_real, elim_rem, udiv2mul, split_concat_eq, bit2bool, blast_eq_value, elim_sign_ext, hi_div0, mul2concat, bvnot2arith, bv_sort_ac, bv_trailing, expand_select_store, expand_store_eq, sort_store, max_memory, max_steps, push_ite_arith, push_ite_bv, pull_cheap_ite, cache_all, max_rounds, solve_eqs_max_occs, theory_solver, ite_solver, max_args, div0_ackermann_limit, candidate_models, fail_if_inconclusive, auto_config, logic, random_seed, relevancy, macro_finder, ematching, phase_selection, restart_strategy, restart_factor, case_split, delay_units, delay_units_threshold, pull_nested_quantifiers, refine_inj_axioms, timeout, rlimit, max_conflicts, mbqi, mbqi.max_cexs, mbqi.max_cexs_incr, mbqi.max_iterations, mbqi.trace, mbqi.force_template, mbqi.id, qi.profile, qi.profile_freq, qi.max_instances, qi.eager_threshold, qi.lazy_threshold, qi.cost, qi.max_multi_patterns, bv.reflect, bv.enable_int2bv, arith.random_initial_value, arith.solver, arith.nl, arith.nl.gb, arith.nl.branching, arith.nl.rounds, arith.euclidean_solver, arith.propagate_eqs, arith.propagation_mode, arith.branch_cut_ratio, arith.int_eq_branch, arith.ignore_int, arith.dump_lemmas, arith.greatest_error_pivot, pb.conflict_frequency, pb.learn_complements, pb.enable_compilation, pb.enable_simplex, array.weak, array.extensional, dack, dack.eq, dack.factor, dack.gc, dack.gc_inv_decay, dack.threshold, core.validate, blast_mul, blast_add, blast_quant, blast_full, aig_per_assertion, ite_extra, learned, phase, phase.caching.on, phase.caching.off, restart, restart.initial, restart.factor, random_freq, burst_search, gc, gc.initial, gc.increment, gc.small_lbd, gc.k, minimize_lemmas, dyn_sub_res, minimize_core, minimize_core_partial, optimize_model, bcd, dimacs.core, elim_blocked_clauses, elim_blocked_clauses_at, blocked_clause_limit, resolution, resolution.limit, resolution.occ_cutoff, resolution.occ_cutoff_range1, resolution.occ_cutoff_range2, resolution.occ_cutoff_range3, resolution.lit_cutoff_range1, resolution.lit_cutoff_range2, resolution.lit_cutoff_range3, resolution.cls_cutoff1, resolution.cls_cutoff2, elim_vars, subsumption, subsumption.limit, asymm_branch, asymm_branch.rounds, asymm_branch.limit, scc, max_depth, propagate_eq, add_bound_lower, add_bound_upper, produce_models, norm_int_only, lia2pb_partial, lia2pb_max_bits, lia2pb_total_bits, pb2bv_all_clauses_limit, pb2bv_cardinality_limit, flat, elim_and, flat, elim_and, flat, elim_and, flat, elim_and, sk_hack, mode, ignore_labels, skolemize, complete, elim_root_objects, elim_inverses, split_factors, max_search_size, max_prime, num_primes, common_patterns, distributivity, distributivity_blowup, ite_chaing, factor, zero_accuracy, min_mag, factor_max_prime, factor_num_primes, factor_search_size, lazy, reorder, simplify_conflicts, minimize_conflicts, randomize, shuffle_vars, seed, nla2bv_max_bv_size, nla2bv_bv_size, nla2bv_root, nla2bv_divisor, cofactor_equalities, qe_nonlinear, eliminate_variables_as_block, solver2_timeout, ignore_solver1, solver2_unknown, proof, model, unsat_core)
                                     })
                ; we need guards to be convex in order for the tS...t0 split to make sense! Later, use
                ; quantifier instantiation where possible and forbid
                ; <state sequence, quantifier choice sequence> pairs from the model
                _ (assert (nil? ha.eval/guard-memo))
                _ (assert (every? keyword? (keys (get-in ha-defs [:f1]))))
                ha-defs (desugar/guard-disjunctions-to-transitions ha-defs)
                _ (assert (nil? ha.eval/guard-memo))
                _ (assert (every? keyword? (keys (get-in ha-defs [:f1]))))
                ha-defs (desugar/simplify-guards ha-defs z3)
                _ (assert (every? keyword? (keys (get-in ha-defs [:f1]))))
                _ (assert (nil? ha.eval/guard-memo))
                z3 (z3/update-ha-defs z3 ha-defs)
                _ (assert (nil? ha.eval/guard-memo))
                _ (assert (:ha-defs z3))
                entry-time (apply max (map :entry-time (vals ha-vals)))
                _ (assert (nil? ha.eval/guard-memo))
                [ha-vals tr-caches] (heval/init-has ha-defs (vals ha-vals) entry-time)
                _ (assert (nil? ha.eval/guard-memo))
                config {:objects    ha-vals
                        :entry-time entry-time
                        :tr-caches  tr-caches
                        :inputs     #{}}
                _ (println "defs" ha-defs)
                _ (println "vals" ha-vals config)
                [_reqs opts] (roll/next-transitions config)
                _ (println "trs" (count _reqs) (count opts))
                ; so for each optional transition available
                times (doall
                        (for [{intvl                    :interval
                               {target :target
                                index  :index :as edge} :transition
                               ha-id                    :id :as o} opts
                              :let
                              [tS (iv/start intvl)
                               tE (iv/end intvl)
                               _ (println "opt" index tS tE)
                               ha (get-in config [:objects ha-id])
                               ha-type (.-ha-type ha)
                               _ (assert (:ha-defs z3))
                               ; solve for values of t0 in tS...tE.
                               worlds (z3/with-solver
                                        z3
                                        (fn [z3]
                                          (assert (or (:solver z3) (:optimizer z3)))
                                          (assert (:ha-defs z3))
                                          (let [z3 (z3/assert-valuation! z3 (:objects config) "t00")
                                                _ (assert (:has z3))
                                                _ (assert (or (:solver z3) (:optimizer z3)))
                                                _ (assert (:ha-defs z3))
                                                z3 (z3/assert-flow-jump! z3 ha-id edge "t0")
                                                _ (assert (or (:solver z3) (:optimizer z3)))
                                                z3 (z3/assert-all! z3 [[:gt "t0" "t00"]
                                                                       [:geq "t0" tS]
                                                                       [:leq "t0" (min tE (+ tS lookahead-time))]])
                                                _ (assert (or (:solver z3) (:optimizer z3)))
                                                status (z3/check! z3)
                                                _ (assert (= status :sat))
                                                [z3 time-steps] (z3/symx! z3 2)
                                                found-intervals
                                                (loop [found-intervals #{}
                                                       z3 z3]
                                                  (assert (:has z3))
                                                  (println "constraint set ok?" found-intervals)
                                                  (if (= :sat (ha/spy "status:" (z3/check! z3)))
                                                    ; add this interval and then forbid the particular trace
                                                    (let [z3 (z3/push! z3)
                                                          _ (assert (:has z3))
                                                          pcs (z3/path-constraints z3 time-steps)
                                                          ; assert the path constraints and get min/max t0
                                                          z3 (z3/assert-all! z3 [pcs])
                                                          tmin (z3/min-value z3 "t0")
                                                          tmax (z3/max-value z3 "t0")
                                                          z3 (z3/pop! z3)
                                                          _ (println "tmin" tmin "tmax" tmax)
                                                          t-i (ha/spy "found interval" (iv/interval tmin tmax))
                                                          ; asser that future paths don't use these constraints
                                                          z3 (z3/assert-all! z3 [[:not pcs]])
                                                          ;find minimal splits of t0 wrt existing splits
                                                          ; if this new split does not overlap any splits, just add it.
                                                          overlapping-intervals (sort-by :start (filter #(iv/intersection t-i %) found-intervals))]
                                                      (recur (conj found-intervals t-i) z3))
                                                    found-intervals))]
                                            ;break up found-intervals?
                                            found-intervals)))
                               sorted-worlds (sort-by :start (set worlds))]]
                          [o sorted-worlds]))]
            (transit/write (ha/transit-writer out-stream)
                           (ha/spy "ret" times)))))
      {:status  200
       :headers {"Content-Type" "application/json"}
       :body    (str "\"" (string/escape (.toString out-stream) {\" "\\\""}) "\"")})))

(def handler
  (-> #'rpc-handler
      (wrap-reload)
      wrap-keyword-params
      wrap-nested-params
      wrap-params))

#_(defonce server (rs/serve services {:port 4445 :join false}))

;(defn start [] nil)
;(defn stop [] nil)

#_(defn start [] (.start server))
#_(defn stop [] (.stop server))
