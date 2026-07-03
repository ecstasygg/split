theory Reuse
  imports Snapshot
begin

definition vacant :: "nat \<Rightarrow> pager \<Rightarrow> nat \<Rightarrow> bool" where
  "vacant slots s f = list_all (\<lambda>k. ptable s k \<noteq> f) [0..<slots]"

lemma vacant_iff [simp]:
  "vacant slots s f \<longleftrightarrow> (\<forall>k<slots. ptable s k \<noteq> f)"
  by (auto simp: vacant_def list_all_iff)

definition copy_frame :: "pager \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pager" where
  "copy_frame s k f = s\<lparr>ptable := (ptable s)(k := f),
    physical := (physical s)(f := view s k), writable := (writable s)(k := True),
    frontier := max (frontier s) (Suc f)\<rparr>"

definition clear_slot :: "nat \<Rightarrow> pager \<Rightarrow> nat \<Rightarrow> pager" where
  "clear_slot pages s k = s\<lparr>ptable := (ptable s)(k := k mod pages),
    physical := (physical s)(ptable s k := (\<lambda>_. 0)), writable := (writable s)(k := False)\<rparr>"

definition pooled :: "nat \<Rightarrow> nat \<Rightarrow> pager \<Rightarrow> nat list \<Rightarrow> bool" where
  "pooled pages slots s available \<longleftrightarrow>
    invariant slots s \<and> private_frames pages slots s \<and> distinct available \<and>
    (\<forall>f\<in>set available. pages \<le> f \<and> f < frontier s \<and>
      vacant slots s f \<and> physical s f = (\<lambda>_. 0))"

definition reserve :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pager \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> (pager \<times> nat list) option" where
  "reserve pages slots capacity s available k =
    (let f = (case available of [] \<Rightarrow> frontier s | x # xs \<Rightarrow> x) in
     if 0 < pages \<and> k < slots \<and> \<not> writable s k \<and> pages \<le> f \<and>
        f < capacity \<and> vacant slots s f
     then Some (copy_frame s k f, tl available) else None)"

definition reclaim :: "nat \<Rightarrow> nat \<Rightarrow> pager \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> (pager \<times> nat list) option" where
  "reclaim pages slots s available k =
    (if 0 < pages \<and> k < slots \<and> writable s k \<and> pages \<le> ptable s k \<and>
      ptable s k \<notin> set available \<and>
      list_all (\<lambda>j. j = k \<or> ptable s j \<noteq> ptable s k) [0..<slots]
     then Some (clear_slot pages s k, ptable s k # available) else None)"

lemma initial_pooled:
  "0 < pages \<Longrightarrow> pooled pages slots (initial pages contents) []"
  by (simp add: pooled_def initial_invariant initial_private)

lemma copy_view:
  "vacant slots s f \<Longrightarrow> j < slots \<Longrightarrow> view (copy_frame s k f) j = view s j"
  by (auto simp: view_def copy_frame_def)

lemma copy_bounded:
  "bounded slots s \<Longrightarrow> bounded slots (copy_frame s k f)"
  by (auto simp: bounded_def copy_frame_def max_def)

lemma copy_exclusive:
  "exclusive slots s \<Longrightarrow> vacant slots s f \<Longrightarrow> exclusive slots (copy_frame s k f)"
  by (auto simp: exclusive_def copy_frame_def split: if_splits)

lemma copy_invariant:
  "invariant slots s \<Longrightarrow> vacant slots s f \<Longrightarrow> invariant slots (copy_frame s k f)"
  by (simp add: invariant_def copy_bounded copy_exclusive)

lemma copy_private:
  "private_frames pages slots s \<Longrightarrow> pages \<le> f \<Longrightarrow>
   private_frames pages slots (copy_frame s k f)"
  by (auto simp: private_frames_def copy_frame_def max_def)

lemma copy_original:
  "pages \<le> f \<Longrightarrow> original < pages \<Longrightarrow>
   physical (copy_frame s k f) original = physical s original"
  by (auto simp: copy_frame_def)

lemma clear_bounded:
  "0 < pages \<Longrightarrow> bounded slots s \<Longrightarrow> pages \<le> frontier s \<Longrightarrow>
   bounded slots (clear_slot pages s k)"
  by (auto simp: bounded_def clear_slot_def intro: less_le_trans[OF mod_less_divisor])

lemma clear_exclusive:
  "0 < pages \<Longrightarrow> exclusive slots s \<Longrightarrow> private_frames pages slots s \<Longrightarrow>
   exclusive slots (clear_slot pages s k)"
  by (auto simp: exclusive_def private_frames_def clear_slot_def split: if_splits; metis mod_less_divisor not_le)

lemma clear_private:
  "private_frames pages slots s \<Longrightarrow> private_frames pages slots (clear_slot pages s k)"
  by (auto simp: private_frames_def clear_slot_def)

lemma clear_invariant:
  "0 < pages \<Longrightarrow> invariant slots s \<Longrightarrow> private_frames pages slots s \<Longrightarrow>
   invariant slots (clear_slot pages s k)"
  by (metis invariant_def private_frames_def clear_bounded clear_exclusive)

lemma clear_vacant:
  "0 < pages \<Longrightarrow> exclusive slots s \<Longrightarrow> k < slots \<Longrightarrow>
   writable s k \<Longrightarrow> pages \<le> ptable s k \<Longrightarrow>
   vacant slots (clear_slot pages s k) (ptable s k)"
  by (auto simp: exclusive_def clear_slot_def; metis mod_less_divisor not_le)

lemma clear_other_view:
  "exclusive slots s \<Longrightarrow> k < slots \<Longrightarrow> writable s k \<Longrightarrow>
   j < slots \<Longrightarrow> j \<noteq> k \<Longrightarrow> view (clear_slot pages s k) j = view s j"
  by (auto simp: exclusive_def clear_slot_def view_def)

lemma clear_target_view:
  "0 < pages \<Longrightarrow> pages \<le> ptable s k \<Longrightarrow>
   view (clear_slot pages s k) k = physical s (k mod pages)"
  by (auto simp: clear_slot_def view_def; metis mod_less_divisor not_le)

lemma clear_original:
  "pages \<le> ptable s k \<Longrightarrow> f < pages \<Longrightarrow>
   physical (clear_slot pages s k) f = physical s f"
  by (auto simp: clear_slot_def)

theorem reclaim_zero:
  "reclaim pages slots s available k = Some (t, remaining) \<Longrightarrow>
   physical t (ptable s k) = (\<lambda>_. 0)"
  by (auto simp: reclaim_def clear_slot_def split: if_splits)

theorem reclaim_unmapped:
  assumes pool: "pooled pages slots s available"
    and step: "reclaim pages slots s available k = Some (t, remaining)"
  shows "vacant slots t (ptable s k)"
  using pool step
  by (auto simp: reclaim_def pooled_def invariant_def split: if_splits; metis clear_vacant vacant_iff)

theorem reclaim_views:
  assumes "pooled pages slots s available"
    "reclaim pages slots s available k = Some (t, remaining)" "j < slots"
  shows "view t j = (if j = k then physical s (k mod pages) else view s j)"
  using assms clear_other_view clear_target_view
  by (auto simp: pooled_def reclaim_def invariant_def split: if_splits)

theorem reclaim_pool:
  assumes pool: "pooled pages slots s available"
    and step: "reclaim pages slots s available k = Some (t, remaining)"
  shows "pooled pages slots t remaining"
proof -
  have positive: "0 < pages" and valid: "k < slots" and writable: "writable s k"
    and private_frame: "pages \<le> ptable s k" and fresh: "ptable s k \<notin> set available"
    and result: "t = clear_slot pages s k" "remaining = ptable s k # available"
    using step by (auto simp: reclaim_def split: if_splits)
  have inv: "invariant slots s" and owned: "private_frames pages slots s"
    using pool by (auto simp: pooled_def)
  have new_inv: "invariant slots t" and new_owned: "private_frames pages slots t"
    using clear_invariant[OF positive inv owned] clear_private[OF owned] result by auto
  have unused: "vacant slots t (ptable s k)"
    using reclaim_unmapped[OF pool step] .
  have clean: "physical t (ptable s k) = (\<lambda>_. 0)"
    using reclaim_zero[OF step] .
  show ?thesis
    using pool fresh result positive valid private_frame inv new_inv new_owned unused clean
    by (auto simp: pooled_def clear_slot_def bounded_def invariant_def split: if_splits; metis mod_less_divisor not_le)
qed

theorem reserve_views:
  "reserve pages slots capacity s available k = Some (t, remaining) \<Longrightarrow>
   j < slots \<Longrightarrow> view t j = view s j"
  by (auto simp: reserve_def Let_def split: list.splits if_splits intro: copy_view)

theorem reserve_pool:
  assumes pool: "pooled pages slots s available"
    and step: "reserve pages slots capacity s available k = Some (t, remaining)"
  shows "pooled pages slots t remaining"
proof (cases available)
  case Nil
  then have fresh: "vacant slots s (frontier s)"
    using pool by (auto simp: pooled_def invariant_def bounded_def)
  have owned: "pages \<le> frontier s" using pool by (auto simp: pooled_def private_frames_def)
  show ?thesis
    using step pool fresh owned Nil copy_invariant copy_private
    by (auto simp: reserve_def Let_def pooled_def split: if_splits)
next
  case (Cons f rest)
  have fresh: "vacant slots s f" and owned: "pages \<le> f"
    and distinct: "f \<notin> set rest"
    using pool Cons by (auto simp: pooled_def)
  have result: "t = copy_frame s k f" "remaining = rest"
    using step Cons by (auto simp: reserve_def Let_def split: if_splits)
  have inv: "invariant slots t" and own: "private_frames pages slots t"
    using pool result fresh owned copy_invariant copy_private by (auto simp: pooled_def)
  show ?thesis
    using pool Cons distinct result inv own
    by (auto simp: pooled_def copy_frame_def max_def split: if_splits)
qed

theorem reserve_original:
  "reserve pages slots capacity s available k = Some (t, remaining) \<Longrightarrow>
   f < pages \<Longrightarrow> physical t f = physical s f"
  by (auto simp: reserve_def Let_def split: list.splits if_splits intro: copy_original)

theorem reclaim_original:
  "reclaim pages slots s available k = Some (t, remaining) \<Longrightarrow>
   f < pages \<Longrightarrow> physical t f = physical s f"
  by (auto simp: reclaim_def split: if_splits intro: clear_original)

theorem pooled_unmapped:
  "pooled pages slots s available \<Longrightarrow> f \<in> set available \<Longrightarrow>
   j < slots \<Longrightarrow> ptable s j \<noteq> f"
  by (auto simp: pooled_def)

theorem pooled_clean:
  "pooled pages slots s available \<Longrightarrow> f \<in> set available \<Longrightarrow>
   physical s f offset = 0"
  by (auto simp: pooled_def)

theorem pooled_store:
  assumes "pooled pages slots s available" "k < slots" "writable s k"
  shows "pooled pages slots (store s k offset byte) available"
  using assms write_invariant[of slots s k offset byte] store_private[of pages slots s k offset byte]
  by (auto simp: pooled_def store_def prepare_def Let_def)

end
