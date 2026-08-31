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

end
