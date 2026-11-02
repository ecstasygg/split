theory Snapshot
  imports Protocol
begin

definition private_frames :: "nat \<Rightarrow> nat \<Rightarrow> pager \<Rightarrow> bool" where
  "private_frames pages slots s \<longleftrightarrow> pages \<le> frontier s \<and>
    (\<forall>k<slots. writable s k \<longrightarrow> pages \<le> ptable s k)"

lemma initial_private: "private_frames pages slots (initial pages contents)"
  by (simp add: private_frames_def)

lemma prepare_private:
  "private_frames pages slots s \<Longrightarrow> private_frames pages slots (prepare s k)"
  by (auto simp: private_frames_def prepare_def split: if_splits)

lemma prepared_frame_private:
  "private_frames pages slots s \<Longrightarrow> k < slots \<Longrightarrow>
   pages \<le> ptable (prepare s k) k"
  by (auto simp: private_frames_def prepare_def)

lemma store_private:
  "private_frames pages slots s \<Longrightarrow> private_frames pages slots (store s k offset byte)"
  using prepare_private[of pages slots s k]
  by (simp add: private_frames_def)

lemma prepare_original:
  "private_frames pages slots s \<Longrightarrow> f < pages \<Longrightarrow>
   physical (prepare s k) f = physical s f"
  by (auto simp: private_frames_def prepare_def detach_def)

theorem store_original:
  assumes owned: "private_frames pages slots s" and valid: "k < slots" and original: "f < pages"
  shows "physical (store s k offset byte) f = physical s f"
proof -
  have distinct: "f \<noteq> ptable (prepare s k) k"
    using prepared_frame_private[OF owned valid] original by arith
  have preserved: "physical (prepare s k) f = physical s f"
    using prepare_original[OF owned original] .
  show ?thesis
    using distinct preserved by (simp add: store_def Let_def)
qed

lemma advance_private:
  "private_frames pages slots s \<Longrightarrow> private_frames pages slots (advance s a)"
  by (cases a; simp add: store_private)

lemma advance_original:
  "private_frames pages slots s \<Longrightarrow> valid slots bytes a \<Longrightarrow> f < pages \<Longrightarrow>
   physical (advance s a) f = physical s f"
  by (cases a; auto intro: store_original)

theorem execute_original:
  "private_frames pages slots s \<Longrightarrow> list_all (valid slots bytes) actions \<Longrightarrow>
   f < pages \<Longrightarrow> physical (execute s actions) f = physical s f"
proof (induction actions arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a actions)
  have state: "private_frames pages slots (advance s a)"
    using Cons.prems by (simp add: advance_private)
  have tail: "physical (execute (advance s a) actions) f = physical (advance s a) f"
    using Cons.IH[OF state] Cons.prems by simp
  show ?case
    using tail advance_original Cons.prems by auto
qed

corollary original_preserved:
  "list_all (valid slots bytes) actions \<Longrightarrow> f < pages \<Longrightarrow>
   physical (execute (initial pages contents) actions) f = contents f"
  using execute_original[OF initial_private] by simp

definition promote :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pager \<Rightarrow> pager" where
  "promote pages slots source s =
    s\<lparr>ptable := (\<lambda>k. if slots \<le> k \<and> k < slots + pages
      then ptable s (source + (k - slots)) else ptable s k),
      writable := (\<lambda>k. writable s k \<and> \<not> (source \<le> k \<and> k < source + pages)
        \<and> \<not> (slots \<le> k \<and> k < slots + pages))\<rparr>"

lemma promotion_live_view:
  "k < slots \<Longrightarrow> view (promote pages slots source s) k = view s k"
  by (simp add: promote_def view_def)

lemma promotion_baseline_view:
  "p < pages \<Longrightarrow>
   view (promote pages slots source s) (slots + p) = view s (source + p)"
  by (simp add: promote_def view_def)

lemma promotion_baseline_readonly:
  "p < pages \<Longrightarrow> \<not> writable (promote pages slots source s) (slots + p)"
  by (simp add: promote_def)

lemma promotion_source_readonly:
  "p < pages \<Longrightarrow> \<not> writable (promote pages slots source s) (source + p)"
  by (simp add: promote_def)

lemma promotion_bounded:
  assumes bounds: "bounded (slots + pages) s" and source: "source + pages \<le> slots"
  shows "bounded (slots + pages) (promote pages slots source s)"
proof (unfold bounded_def, intro allI impI)
  fix k
  assume live: "k < slots + pages"
  show "ptable (promote pages slots source s) k < frontier (promote pages slots source s)"
  proof (cases "slots \<le> k")
    case True
    have selected: "source + (k - slots) < slots + pages"
      using source live True by arith
    show ?thesis
      using bounded_frame[OF bounds selected] live True by (simp add: promote_def)
  next
    case False
    show ?thesis
      using bounded_frame[OF bounds live] False by (simp add: promote_def)
  qed
qed

lemma promotion_exclusive:
  assumes owned: "exclusive (slots + pages) s" and source: "source + pages \<le> slots"
  shows "exclusive (slots + pages) (promote pages slots source s)"
proof (unfold exclusive_def, intro allI impI)
  fix k j
  assume live: "k < slots + pages" "j < slots + pages"
    and access: "writable (promote pages slots source s) k"
    and sharing: "ptable (promote pages slots source s) j = ptable (promote pages slots source s) k"
  have writable: "writable s k" and outside: "\<not> (source \<le> k \<and> k < source + pages)"
    and old: "ptable (promote pages slots source s) k = ptable s k"
    using access by (auto simp: promote_def)
  show "j = k"
  proof (cases "slots \<le> j")
    case True
    have selected: "source + (j - slots) < slots + pages"
      and inside: "source \<le> source + (j - slots) \<and> source + (j - slots) < source + pages"
      using source live True by arith+
    have frame: "ptable s (source + (j - slots)) = ptable s k"
      using sharing old live True by (simp add: promote_def)
    have "source + (j - slots) = k"
      using writable_unique[OF owned live(1) selected writable frame] .
    then show ?thesis using inside outside by simp
  next
    case False
    have "ptable s j = ptable s k"
      using sharing old False by (simp add: promote_def)
    then show ?thesis
      using writable_unique[OF owned live writable] by simp
  qed
qed

theorem promotion_invariant:
  "invariant (slots + pages) s \<Longrightarrow> source + pages \<le> slots \<Longrightarrow>
   invariant (slots + pages) (promote pages slots source s)"
  by (simp add: invariant_def promotion_bounded promotion_exclusive)

theorem promotion_preserves_unselected:
  assumes "k < slots" "k < source \<or> source + pages \<le> k"
  shows "view (promote pages slots source s) k = view s k \<and>
    writable (promote pages slots source s) k = writable s k"
  using assms by (auto simp: promote_def view_def)

theorem promotion_store_preserves_unselected:
  assumes inv: "invariant (slots + pages) s" and source: "source + pages \<le> slots"
    and page: "p < pages" and live: "k < slots"
    and unselected: "k < source \<or> source + pages \<le> k"
  shows "view (store (promote pages slots source s) (source + p) offset byte) k = view s k"
proof -
  have selected: "source + p < slots + pages" and other: "k \<noteq> source + p"
    using source page live unselected by arith+
  show ?thesis
    using write_other[OF promotion_invariant[OF inv source] selected _ other] live
    by (simp add: promotion_live_view)
qed

theorem promotion_store_preserves_baseline:
  assumes inv: "invariant (slots + pages) s" and source: "source + pages \<le> slots"
    and pages: "p < pages" "q < pages"
  shows "view (store (promote pages slots source s) (source + p) offset byte) (slots + q) =
    view s (source + q)"
proof -
  have selected: "source + p < slots + pages" and baseline: "slots + q < slots + pages"
    and other: "slots + q \<noteq> source + p"
    using source pages by arith+
  show ?thesis
    using write_other[OF promotion_invariant[OF inv source] selected baseline other]
    by (simp add: promotion_baseline_view pages)
qed

end
