theory Isolation
  imports Model
begin

lemma write_target:
  assumes "bounded n s" "k < n"
  shows "view (store s k offset byte) k = (view s k)(offset := byte)"
  using prepare_view[OF assms, of k]
  by (simp add: view_def store_def Let_def)

lemma write_other:
  assumes inv: "invariant n s" and valid: "k < n" "j < n" and different: "j \<noteq> k"
  shows "view (store s k offset byte) j = view s j"
proof -
  have prepared: "invariant n (prepare s k)"
    using inv by (rule prepare_invariant)
  have distinct: "ptable (prepare s k) j \<noteq> ptable (prepare s k) k"
    using writable_unique[of n "prepare s k" k j] prepared valid different
    by (auto simp: invariant_def)
  have preserved: "view (prepare s k) j = view s j"
    using prepare_view[of n s j k] inv valid by (auto simp: invariant_def)
  show ?thesis
    using distinct preserved by (simp add: store_def view_def Let_def)
qed

theorem write_refinement:
  assumes "invariant n s" "k < n" "j < n"
  shows "view (store s k offset byte) j =
    (if j = k then (view s k)(offset := byte) else view s j)"
  using assms write_target write_other by (auto simp: invariant_def)

corollary read_after_write:
  "invariant n s \<Longrightarrow> k < n \<Longrightarrow>
   view (store s k offset byte) k offset = byte"
  using write_refinement[of n s k k offset byte] by simp

corollary other_offset:
  "invariant n s \<Longrightarrow> k < n \<Longrightarrow> address \<noteq> offset \<Longrightarrow>
   view (store s k offset byte) k address = view s k address"
  using write_refinement[of n s k k offset byte] by simp

definition reference_write :: "memory \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memory" where
  "reference_write m k offset byte = m(k := (m k)(offset := byte))"

definition represents :: "nat \<Rightarrow> pager \<Rightarrow> memory \<Rightarrow> bool" where
  "represents n s m \<longleftrightarrow> (\<forall>k<n. view s k = m k)"

lemma represents_initial:
  "represents n (initial pages contents) (\<lambda>k. contents (k mod pages))"
  by (simp add: represents_def)

theorem simulation:
  assumes "invariant n s" "represents n s m" "k < n"
  shows "represents n (store s k offset byte) (reference_write m k offset byte)"
  using assms write_refinement[of n s k]
  by (auto simp: represents_def reference_write_def)

lemma prepared_exclusive:
  "invariant n s \<Longrightarrow> k < n \<Longrightarrow> j < n \<Longrightarrow> j \<noteq> k \<Longrightarrow>
   ptable (prepare s k) j \<noteq> ptable (prepare s k) k"
  using prepare_invariant writable_unique prepare_writable
  unfolding invariant_def by blast

lemma writable_no_copy:
  "writable s k \<Longrightarrow> frontier (store s k offset byte) = frontier s"
  by (simp add: prepare_def)

lemma readonly_one_copy:
  "\<not> writable s k \<Longrightarrow> frontier (store s k offset byte) = Suc (frontier s)"
  by (simp add: prepare_def)

lemma subsequent_write_no_copy:
  "frontier (store (store s k a x) k b y) = frontier (store s k a x)"
  by (rule writable_no_copy) simp

lemma write_writable_target [simp]: "writable (store s k offset byte) k"
  by simp

lemma write_writable_other:
  "j \<noteq> k \<Longrightarrow> writable (store s k offset byte) j = writable s j"
  by (simp add: prepare_def)

lemma write_preserves_unallocated:
  "f > frontier s \<Longrightarrow> physical (store s k offset byte) f = physical s f"
  if "bounded n s" "k < n" for f s k n offset byte
  using that bounded_frame[OF that]
  by (auto simp: store_def prepare_def detach_def Let_def split: if_splits)

end
