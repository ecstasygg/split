theory Model
  imports Main
begin

type_synonym page = "nat \<Rightarrow> nat"
type_synonym memory = "nat \<Rightarrow> page"

record pager =
  ptable :: "nat \<Rightarrow> nat"
  physical :: memory
  writable :: "nat \<Rightarrow> bool"
  frontier :: nat

definition view :: "pager \<Rightarrow> memory" where
  "view s k = physical s (ptable s k)"

definition bounded :: "nat \<Rightarrow> pager \<Rightarrow> bool" where
  "bounded n s \<longleftrightarrow> (\<forall>k<n. ptable s k < frontier s)"

definition exclusive :: "nat \<Rightarrow> pager \<Rightarrow> bool" where
  "exclusive n s \<longleftrightarrow>
    (\<forall>k<n. writable s k \<longrightarrow> (\<forall>j<n. ptable s j = ptable s k \<longrightarrow> j = k))"

definition invariant :: "nat \<Rightarrow> pager \<Rightarrow> bool" where
  "invariant n s \<longleftrightarrow> bounded n s \<and> exclusive n s"

definition initial :: "nat \<Rightarrow> memory \<Rightarrow> pager" where
  "initial pages contents =
    \<lparr>ptable = (\<lambda>k. k mod pages), physical = contents,
     writable = (\<lambda>_. False), frontier = pages\<rparr>"

definition detach :: "pager \<Rightarrow> nat \<Rightarrow> pager" where
  "detach s k = s\<lparr>ptable := (ptable s)(k := frontier s),
    physical := (physical s)(frontier s := view s k),
    writable := (writable s)(k := True), frontier := Suc (frontier s)\<rparr>"

definition prepare :: "pager \<Rightarrow> nat \<Rightarrow> pager" where
  "prepare s k = (if writable s k then s else detach s k)"

definition store :: "pager \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pager" where
  "store s k offset byte = (let t = prepare s k in
    t\<lparr>physical := (physical t)(ptable t k := (view t k)(offset := byte))\<rparr>)"

lemma initial_ptable [simp]: "ptable (initial pages contents) k = k mod pages"
  by (simp add: initial_def)

lemma initial_physical [simp]: "physical (initial pages contents) = contents"
  by (simp add: initial_def)

lemma initial_writable [simp]: "\<not> writable (initial pages contents) k"
  by (simp add: initial_def)

lemma initial_frontier [simp]: "frontier (initial pages contents) = pages"
  by (simp add: initial_def)

lemma initial_view [simp]: "view (initial pages contents) k = contents (k mod pages)"
  by (simp add: view_def)

lemma initial_bounded:
  "0 < pages \<Longrightarrow> bounded n (initial pages contents)"
  by (simp add: bounded_def)

lemma initial_exclusive: "exclusive n (initial pages contents)"
  by (simp add: exclusive_def)

theorem initial_invariant:
  "0 < pages \<Longrightarrow> invariant n (initial pages contents)"
  by (simp add: invariant_def initial_bounded initial_exclusive)

lemma bounded_frame:
  "bounded n s \<Longrightarrow> k < n \<Longrightarrow> ptable s k < frontier s"
  by (simp add: bounded_def)

lemma fresh_frame:
  "bounded n s \<Longrightarrow> k < n \<Longrightarrow> ptable s k \<noteq> frontier s"
  using bounded_frame by fastforce

lemma writable_unique:
  "exclusive n s \<Longrightarrow> k < n \<Longrightarrow> j < n \<Longrightarrow>
   writable s k \<Longrightarrow> ptable s j = ptable s k \<Longrightarrow> j = k"
  by (auto simp: exclusive_def)

lemma detach_ptable [simp]:
  "ptable (detach s k) j = (if j = k then frontier s else ptable s j)"
  by (simp add: detach_def)

lemma detach_writable [simp]:
  "writable (detach s k) j = (j = k \<or> writable s j)"
  by (simp add: detach_def)

lemma detach_frontier [simp]: "frontier (detach s k) = Suc (frontier s)"
  by (simp add: detach_def)

lemma detach_copy [simp]: "physical (detach s k) (frontier s) = view s k"
  by (simp add: detach_def)

lemma detach_other_frame:
  "f \<noteq> frontier s \<Longrightarrow> physical (detach s k) f = physical s f"
  by (simp add: detach_def)

lemma detach_target_view [simp]: "view (detach s k) k = view s k"
  by (simp add: view_def detach_def)

lemma detach_view:
  assumes "bounded n s" "j < n"
  shows "view (detach s k) j = view s j"
  using fresh_frame[OF assms] by (auto simp: view_def detach_def)

lemma detach_bounded:
  "bounded n s \<Longrightarrow> bounded n (detach s k)"
  by (auto simp: bounded_def less_Suc_eq_le)

lemma detach_exclusive:
  assumes "bounded n s" "exclusive n s"
  shows "exclusive n (detach s k)"
  using assms by (auto simp: exclusive_def bounded_def split: if_splits)

theorem detach_invariant:
  "invariant n s \<Longrightarrow> invariant n (detach s k)"
  by (simp add: invariant_def detach_bounded detach_exclusive)

lemma prepare_writable [simp]: "writable (prepare s k) k"
  by (simp add: prepare_def)

lemma prepare_invariant:
  "invariant n s \<Longrightarrow> invariant n (prepare s k)"
  by (simp add: prepare_def detach_invariant)

lemma prepare_view:
  "bounded n s \<Longrightarrow> j < n \<Longrightarrow> view (prepare s k) j = view s j"
  by (simp add: prepare_def detach_view)

lemma prepare_frontier:
  "frontier (prepare s k) = frontier s + (if writable s k then 0 else 1)"
  by (simp add: prepare_def)

lemma prepare_ptable_other:
  "j \<noteq> k \<Longrightarrow> ptable (prepare s k) j = ptable s j"
  by (simp add: prepare_def)

lemma prepare_idempotent [simp]: "prepare (prepare s k) k = prepare s k"
  by (simp add: prepare_def detach_def)

lemma write_ptable [simp]: "ptable (store s k offset byte) = ptable (prepare s k)"
  by (simp add: store_def Let_def)

lemma write_writable [simp]: "writable (store s k offset byte) = writable (prepare s k)"
  by (simp add: store_def Let_def)

lemma write_frontier [simp]: "frontier (store s k offset byte) = frontier (prepare s k)"
  by (simp add: store_def Let_def)

theorem write_invariant:
  "invariant n s \<Longrightarrow> invariant n (store s k offset byte)"
  using prepare_invariant[of n s k]
  by (simp add: invariant_def bounded_def exclusive_def)

end
