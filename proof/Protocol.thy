theory Protocol
  imports Execution
begin

definition commit :: "pager \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pager" where
  "commit s k offset byte =
    s\<lparr>physical := (physical s)(ptable s k := (view s k)(offset := byte))\<rparr>"

definition attempt :: "pager \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pager option" where
  "attempt s k offset byte = (if writable s k then Some (commit s k offset byte) else None)"

lemma readonly_faults:
  "\<not> writable s k \<Longrightarrow> attempt s k offset byte = None"
  by (simp add: attempt_def)

lemma writable_commits:
  "writable s k \<Longrightarrow> attempt s k offset byte = Some (store s k offset byte)"
  by (simp add: attempt_def commit_def store_def prepare_def)

lemma resolve_preserves_memory:
  "invariant n s \<Longrightarrow> j < n \<Longrightarrow> view (detach s k) j = view s j"
  using detach_view[of n s j k] by (auto simp: invariant_def)

theorem fault_retry:
  "\<not> writable s k \<Longrightarrow>
   attempt (detach s k) k offset byte = Some (store s k offset byte)"
  by (simp add: attempt_def commit_def store_def prepare_def detach_def)

theorem fault_retry_refinement:
  assumes "invariant n s" "represents n s m" "k < n" "\<not> writable s k"
  obtains t where "attempt (detach s k) k offset byte = Some t"
    "invariant n t" "represents n t (reference_write m k offset byte)"
  using assms fault_retry write_invariant simulation by blast

definition dirty :: "nat \<Rightarrow> pager \<Rightarrow> nat set" where
  "dirty n s = {k. k < n \<and> writable s k}"

lemma finite_dirty [simp]: "finite (dirty n s)"
  unfolding dirty_def by (rule finite_subset[of _ "{..<n}"]) auto

lemma dirty_initial [simp]: "dirty n (initial pages contents) = {}"
  by (auto simp: dirty_def)

lemma dirty_member [simp]: "k \<in> dirty n s \<longleftrightarrow> k < n \<and> writable s k"
  by (simp add: dirty_def)

lemma dirty_store:
  "k < n \<Longrightarrow> dirty n (store s k offset byte) = insert k (dirty n s)"
  by (auto simp: dirty_def prepare_def)

definition accounted :: "nat \<Rightarrow> nat \<Rightarrow> pager \<Rightarrow> bool" where
  "accounted pages slots s \<longleftrightarrow> frontier s = pages + card (dirty slots s)"

lemma initial_accounted: "accounted pages slots (initial pages contents)"
  by (simp add: accounted_def)

lemma store_accounted:
  assumes "accounted pages slots s" "k < slots"
  shows "accounted pages slots (store s k offset byte)"
  using assms
  by (auto simp: accounted_def dirty_store prepare_frontier card_insert_if insert_absorb)

lemma advance_accounted:
  "accounted pages slots s \<Longrightarrow> valid slots bytes a \<Longrightarrow>
   accounted pages slots (advance s a)"
  by (cases a; auto intro: store_accounted)

theorem execute_accounted:
  "accounted pages slots s \<Longrightarrow> list_all (valid slots bytes) actions \<Longrightarrow>
   accounted pages slots (execute s actions)"
  by (induction actions arbitrary: s) (auto intro: advance_accounted)

lemma dirty_card_bound: "card (dirty slots s) \<le> slots"
proof -
  have "dirty slots s \<subseteq> {..<slots}" by (auto simp: dirty_def)
  then have "card (dirty slots s) \<le> card {..<slots}"
    by (intro card_mono) auto
  then show ?thesis by simp
qed

theorem allocation_bound:
  assumes "list_all (valid slots bytes) actions"
  shows "frontier (execute (initial pages contents) actions) \<le> pages + slots"
  using execute_accounted[OF initial_accounted assms] dirty_card_bound
  unfolding accounted_def by fastforce

fun written :: "action list \<Rightarrow> nat set" where
  "written [] = {}"
| "written (Read k offset # actions) = written actions"
| "written (Write k offset byte # actions) = insert k (written actions)"

lemma writable_advance:
  "writable (advance s a) k = (writable s k \<or> k \<in> written [a])"
  by (cases a; auto simp: prepare_def)

theorem written_exactly:
  "writable (execute s actions) k = (writable s k \<or> k \<in> written actions)"
proof (induction actions arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a actions)
  show ?case by (cases a) (auto simp: Cons.IH prepare_def)
qed

theorem copies_exactly:
  assumes "list_all (valid slots bytes) actions"
  shows "frontier (execute (initial pages contents) actions) =
    pages + card ({..<slots} \<inter> written actions)"
proof -
  have "dirty slots (execute (initial pages contents) actions) =
      {..<slots} \<inter> written actions"
    by (auto simp: dirty_def written_exactly)
  then show ?thesis
    using execute_accounted[OF initial_accounted assms] by (simp add: accounted_def)
qed

end
