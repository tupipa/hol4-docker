structure arm_relLib :> arm_relLib =
struct

open HolKernel Parse boolLib bossLib Lib;
open armTheory armLib arm_stepTheory pred_setTheory pairTheory optionTheory;
open arithmeticTheory wordsTheory wordsLib addressTheory combinTheory pairSyntax;
open sumTheory whileTheory;

open arm_relTheory;

infix \\
val op \\ = op THEN;

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
val car = rator
val cdr = rand

val minus_one = EVAL ``-1w:word32``
val minus_one_mult =
  REWRITE_CONV [GSYM minus_one,GSYM WORD_NEG_MUL,GSYM word_sub_def]
   ``x + (0xFFFFFFFFw:word32) * y``
val minus_one_mult = CONJ (RW1 [WORD_ADD_COMM] minus_one_mult) minus_one_mult
val minus_one_mult = CONJ (RW1 [WORD_MULT_COMM] minus_one_mult) minus_one_mult

val state = ``s:arm_state``
val r15 = mk_var("r15",``:word32``)
val p_var = mk_var("p",``:word32``)
val cond_var = mk_var("cond",``:bool``)

val arm_spec_tm = 
  ``ARM_ASSERTION r15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 (SOME n) (SOME z) (SOME c) (SOME v) dm m``

fun add_prime v = mk_var(fst (dest_var v) ^ "'",type_of v)

val (swap_primes,SWAP_PRIMES_RULE) = let
  val vs = (cond_var :: free_vars arm_spec_tm) |> map (fn v => (v,add_prime v))
  val ss = map (fn (x,y) => x |-> y) vs @ map (fn (x,y) => y |-> x) vs
  in (subst ss, INST ss) end

fun remove_aligned_bx th = let
  val tm = cdr (find_term (can (match_term ``aligned_bx (w:word32)``)) (concl th))
  val imp = SPEC tm aligned_bx_lemma
  val th = SIMP_RULE std_ss [imp] (DISCH ((fst o dest_imp o concl) imp) th)
  val th = RW [AND_IMP_INTRO] th
  val th = SIMP_RULE std_ss [ARM_WRITE_STATUS_T_IGNORE_UPDATE] th
  in th end handle HOL_ERR _ => th;

fun collect_term_of_type ty = find_terms (fn tm => type_of tm = ty);

fun process tm = let
  fun is_normal_char c = (* test whether c is 0-9 A-Z a-z or _ *)
    let val v = ord c in (c = #"_") orelse (48 <= v andalso v <=  57)
      orelse (65 <= v andalso v <=  90) orelse (97 <= v andalso v <= 122) end
  fun replace_plus c = if c = #"+" then #"_" else c;
  fun name_of_tm tm =
    "m_" ^ (implode o filter is_normal_char o map replace_plus o explode o term_to_string) tm;
  in if type_of tm = ``:word4`` then let
       val f = int_to_string o numSyntax.int_of_term o snd o dest_comb
       in (tm,mk_var("r" ^ f tm,``:word32``)) end
     else if tm = ``psrN:arm_bit`` then (tm,mk_var("n",``:bool``))
     else if tm = ``psrZ:arm_bit`` then (tm,mk_var("z",``:bool``))
     else if tm = ``psrC:arm_bit`` then (tm,mk_var("c",``:bool``))
     else if tm = ``psrV:arm_bit`` then (tm,mk_var("v",``:bool``))
     else if tm = ``psrQ:arm_bit`` then (tm,mk_var("q",``:bool``))
     else if type_of tm = ``:word32`` then
       (tm,mk_comb(mk_var("m",``:word32->word8``),tm))
     else fail() end;

fun replace_terms p tm = let
  fun aux tm = p tm handle e =>
    if is_comb tm
    then let val (x,y) = dest_comb tm in mk_comb(aux x, aux y) end
    else let val (x,y) = dest_abs tm in mk_abs(x, aux y) end
    handle e => tm
  in aux tm end;

fun rewrite_names tm = let
  fun aux v = let val m = match_term tm (car (car v)) in (snd o process o cdr o car) v end
  in replace_terms aux end;

fun all_distinct [] = []
  | all_distinct (x::xs) =
      if mem x xs then all_distinct xs else x :: all_distinct xs

fun find_terms_all p tm = let
  fun aux tm acc =
    let val acc = if p tm then acc @ [tm] else acc in
      if is_comb tm then let val (x,y) = dest_comb tm in aux y (aux x acc) end else
      if is_abs tm then let val (x,y) = dest_abs tm in aux y acc end else acc end
  in all_distinct (aux tm []) end

fun list_dest f tm = let val (x,y) = f tm in list_dest f x @ list_dest f y end handle e => [tm];


fun arm_pre_post s g = let
  val regs = collect_term_of_type ``:word4`` g
  val regs = filter wordsSyntax.is_n2w regs |> all_distinct
  val bits = collect_term_of_type ``:arm_bit`` g
  val h = rewrite_names ``ARM_READ_STATUS`` (rewrite_names ``ARM_READ_REG`` g)
  val mems1 = find_terms (can (match_term ``ARM_READ_MEM a ^state``)) h
  val mems2 = find_terms (can (match_term ``ARM_WRITE_MEM a x ^state``)) h
  val mems = map (cdr o car) mems1 @ map (cdr o car o car) mems2
  val mems = filter (fn x => not (mem x [``r15 + 3w:word32``,
               ``r15 + 2w:word32``,``r15 + 1w:word32``,r15])) mems
  val addresses = all_distinct mems
  val h2 = rewrite_names ``ARM_READ_MEM`` h
  val reg_assign = find_terms_all (can (match_term ``ARM_WRITE_REG r x ^state``)) h2
  val mem_assign = find_terms_all (can (match_term ``ARM_WRITE_MEM a x ^state``)) h2
  val sts_assign = find_terms_all (can (match_term ``ARM_WRITE_STATUS f x ^state``)) h2
  val assignments = map (fn x => (cdr (car (car x)),cdr (car x))) reg_assign
  val assignments = map (fn x => (cdr (car (car x)),cdr (car x))) mem_assign @ assignments
  val assignments = map (fn x => (cdr (car (car x)),cdr (car x))) sts_assign @ assignments
  val mems = rev (all_distinct mems)
  val code = subst [mk_var("c",``:num``) |->
                    numSyntax.mk_numeral(Arbnum.fromHexString s)]
                   ``(r15:word32,(n2w (c:num)):word32)``
  fun is_pc_relative tm = mem (mk_var("r15",``:word32``)) (free_vars tm)
  val mems_pc_rel = filter is_pc_relative mems
  val has_read_from_mem = (mems_pc_rel = mems) andalso (length mems = 4)
  val (mems,assignments,addresses,code) =
    if not has_read_from_mem then
      (mems,assignments,addresses,subst [mk_var("x",``:word32#word32``)|->code] ``{x:word32#word32}``)
    else let
      val xx = find_term wordsSyntax.is_word_concat h2
      val v = mk_var("pc_rel",``:word32``)
      val addr = (fst o process o last) mems
      val assignments = map (fn (x,y) => (x,subst [xx |-> v]y)) assignments
      val code = subst [mk_var("x",``:word32#word32``)|->code,
                        mk_var("y",``:word32#word32``)|->pairSyntax.mk_pair(addr,v)]
            ``{(x:word32#word32);y}``
      in ([],assignments,[],code) end
  fun get_assigned_value_aux x y [] = y
    | get_assigned_value_aux x y ((q,z)::zs) =
        if x = q then z else get_assigned_value_aux x y zs
  fun get_assigned_value x y = get_assigned_value_aux x y assignments
  fun mk_pre_post_assertion x = let
    val (y,z) = process x
    val q = get_assigned_value x z
    in (z,q) end
  val post_sub = map mk_pre_post_assertion (regs @ bits)
  val m_var = mk_var("m",``:word32 -> word8``) 
  fun mk_mem_update [] = m_var
    | mk_mem_update ((x,y)::xs) =
       if is_var x then mk_mem_update xs else 
       if x = y then mk_mem_update xs else 
        mk_comb(combinSyntax.mk_update(rand x,y),mk_mem_update xs)
  val new_m = mk_mem_update (map mk_pre_post_assertion mems)
  val ss = ((m_var,new_m)::post_sub)
  (* now figure out update to cond *)
  fun match_any [] tm = fail ()
    | match_any (x::xs) tm = match_term x tm handle HOL_ERR _ => match_any xs tm
  fun pass tm = let
    val (s,i) = match_any [``ARM_STATE_OK s``,
                           ``ALIGNED r15``,
                           ``ARM_READ_MEM (r15 + 3w) s = n2w n``,
                           ``ARM_READ_MEM (r15 + 2w) s = n2w n``,
                           ``ARM_READ_MEM (r15 + 1w) s = n2w n``,
                           ``ARM_READ_MEM (r15 + 0w) s = n2w n``,
                           ``ARM_READ_MEM r15 s = n2w n``] tm
    in not (subst s r15 = r15) end handle HOL_ERR _ => true
  val pre_conds = (filter pass o list_dest dest_conj o fst o dest_imp) h
  val pre_conds = filter (not o can (find_term (fn x => x = ``ARM_READ_MEM``))) pre_conds
  val pre_conds = filter (fn x => not (is_neg x andalso is_eq (cdr x) andalso mem r15 (free_vars x))) pre_conds
  fun all_bool tm = (filter (fn x => not (type_of x = ``:bool``)) (free_vars tm)) = []
  val bools = filter all_bool pre_conds
  val pre_conds = if bools = [] then pre_conds else let
                    val pre_bool = (fst o dest_eq o concl o SPEC (list_mk_conj bools)) markerTheory.Abbrev_def
                    in pre_bool :: filter (not o all_bool) pre_conds end
  val pc_post = snd (hd (filter (fn x => (fst x = ``15w:word4``)) assignments))
  val pc = mk_var("r15",``:word32``)
  val pre_conds = if mem pc (free_vars pc_post) then pre_conds else mk_comb(``ALIGNED``,pc_post) :: pre_conds
  val pre_conds = if addresses = [] then pre_conds else
    pre_conds @ [pred_setSyntax.mk_subset(pred_setSyntax.mk_set(addresses),mk_var("dm",``:word32 set``))]
  val post_cond = if pre_conds = [] then cond_var else mk_conj(cond_var,mk_comb(``CONTAINER``,list_mk_conj pre_conds))
  val ss = (cond_var,post_cond)::ss  
  val ss = filter (fn (x,y) => x <> y) ss
  (* formulate abbreviation *)
  fun simple_pc_update (x,y) = (x = r15) andalso mem r15 (free_vars y)
  val ss1 = filter (simple_pc_update) ss
  val ss2 = filter (not o simple_pc_update) ss
  val ss3 = map (fn (x,y) => (x,add_prime x,y)) ss2  
  val pre = mk_pair(arm_spec_tm,cond_var)
  val post = pre |> subst (map (fn (x,y,_) => x |-> y) ss3 @ map (fn (x,y) => x |-> y) ss1)
  val tm1 = map (fn (_,v,_) => v) ss3 |> all_distinct |> pairSyntax.list_mk_pair handle HOL_ERR _ => T
  val tm2 = subst (map (fn (_,v,w) => v |-> w) ss3) tm1
  val assum = mk_eq(tm1,tm2)
  in (assum,pre,code,post) end;

fun annotate_result th = let
  val pat = ``ARM_ASSERTION pc``
  val post = find_term (can (match_term pat)) (th |> concl |> rand) |> rand
  in if can (match_term ``(p:word32) + n2w n``) post then 
       (th,4,SOME (post |> cdr |> cdr |> numSyntax.int_of_term))
     else if can (match_term ``(p:word32) - n2w n``) post then 
       (th,4,SOME (0 - (post |> cdr |> cdr |> numSyntax.int_of_term)))
     else (th,4,NONE) end

val IN_SET_IMP_NEQ = prove(
  ``!(x:'a) y s. x IN s /\ ~(y IN s) ==> ~(x = y)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

val SET_EVERY_lemma = SET_EVERY_def |> INST_TYPE [alpha|->``:'a # 'b``] 
                      |> SIMP_RULE std_ss [FORALL_PROD]

val TRIPLE_ARM_FALSE_POST = prove(
  ``TRIPLE ARM pre code (post,F)``,
  Cases_on `post` \\ SIMP_TAC std_ss [ARM_def,TRIPLE_def,ARM_ASSERT_def]);

fun arm_prove_one_spec s th = let
  val g = concl th
  val next = cdr (find_term (can (match_term ``ARM_NEXT x s = s'``)) g)
  val (assum,pre,code,post) = arm_pre_post s g
  val tm = ``^assum ==> TRIPLE ARM ^pre ^code ^post``
(*
  set_goal([],tm)
*)
  val result = prove(tm,
    SIMP_TAC std_ss []
    \\ REVERSE (Cases_on `^cond_var`) \\ REWRITE_TAC [TRIPLE_ARM_FALSE_POST]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC IMP_ARM_TRIPLE \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `ARM_ASSRT xx yy` MP_TAC
    \\ (CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [ARM_ASSERT_def,IN_INSERT,NOT_IN_EMPTY])))
    \\ STRIP_TAC \\ EXISTS_TAC (cdr next)
    \\ FULL_SIMP_TAC std_ss [ARM_READ_MEM32_IMP,option_assert_def,SET_EVERY_THM]
    \\ STRIP_TAC THEN1   
     (MP_TAC th \\ FULL_SIMP_TAC std_ss [CONTAINER_def,markerTheory.Abbrev_def,ALIGNED_INTRO]
      \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,SET_EVERY_def])
    \\ FULL_SIMP_TAC (srw_ss()) [ARM_ASSERT_def,ARM_READ_WRITE,option_assert_def,
         IN_INSERT,NOT_IN_EMPTY,ALIGNED_INTRO,ARM_READ_MEM32_IMP,SET_EVERY_THM]
    \\ FULL_SIMP_TAC std_ss [ARM_READ_WRITE,ARM_WRITE_STS_INTRO]
    \\ FULL_SIMP_TAC std_ss [CONTAINER_def] \\ IMP_RES_TAC IN_SET_IMP_NEQ
    \\ FULL_SIMP_TAC (srw_ss()) [ARM_ASSERT_def,ARM_READ_WRITE,option_assert_def,
         IN_INSERT,NOT_IN_EMPTY,ALIGNED_INTRO,ARM_READ_MEM32_IMP,SET_EVERY_THM,
         APPLY_UPDATE_THM,ARM_READ_MEM32_def]
    \\ FULL_SIMP_TAC std_ss [SET_EVERY_lemma]
    \\ FULL_SIMP_TAC std_ss [SET_EVERY_def]
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
    \\ IMP_RES_TAC IN_SET_IMP_NEQ
    \\ FULL_SIMP_TAC (srw_ss()) [ARM_READ_WRITE,ARM_WRITE_STS_def]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC IN_SET_IMP_NEQ
    \\ FULL_SIMP_TAC (srw_ss()) [ARM_READ_WRITE,ARM_WRITE_STS_def])
  val result = Q.INST [`r15`|->`p`] result |> GSYM |> RW [] |> UNDISCH_ALL
  in result end;    

(*
fun abbreviate_update th = let
  val pre = th |> concl |> rator |> rator |> rand
  val post = th |> concl |> rand
  val m = fst (match_term pre post) |> map (fn {redex = x, residue = y} => (x,y))
  val new_p = snd (hd (filter (fn (x,_) => x = p_var) m))
  val m1 = filter (fn (x,_) => x <> p_var) m
  val m2 = if mem p_var (free_vars new_p) then m1 else m
*)  

fun arm_spec_aux s = let
  val thms = [arm_step "v6" s]
  val thms = (thms @ [arm_step "v6,fail" s]) handle HOL_ERR _ => thms
  val thms = map (RW [minus_one,minus_one_mult]) thms
  val th = hd thms
  fun derive_spec th = let
    val th = SPEC state th
    val th = RW [ADD_WITH_CARRY_SUB,pairTheory.FST,pairTheory.SND,ADD_WITH_CARRY_SUB_n2w] th
    val th = SIMP_RULE std_ss [] th
    val th = remove_aligned_bx th
    val tm = (fst o dest_eq o concl o SPEC state) ARM_STATE_OK_def
    val th = (RW [AND_IMP_INTRO] o RW [GSYM ARM_STATE_OK_def] o SIMP_RULE bool_ss [ARM_STATE_OK_def] o DISCH tm) th
    val th = SIMP_RULE std_ss [aligned4_thm,aligned2_thm] th
    val th = SIMP_RULE std_ss [word_arith_lemma1] th
    val th = arm_prove_one_spec s th
    val th = CONV_RULE helperLib.FIX_WORD32_ARITH_CONV th    
    val th = SWAP_PRIMES_RULE th
    in th end
  val result = map derive_spec thms
  val result = map annotate_result result  
  in if length result < 2 then (hd result, NONE)
     else (hd result, SOME (result |> tl |> hd)) end

val arm_spec = helperLib.cache arm_spec_aux;
val arm_enc = armLib.arm_encode_from_string;

(*

fun enc s = let val _ = print ("\n\n"^s^"\n\n") in arm_enc s end

  val thms = arm_spec (enc "ADCS r1, r2, r3");
  val thms = arm_spec (enc "TST r5, #3");
  val thms = arm_spec (enc "ADD r1, #10");
  val thms = arm_spec (enc "CMP r1, #10");
  val thms = arm_spec (enc "TST r2, #6");
  val thms = arm_spec (enc "MOV r0, #0");
  val thms = arm_spec (enc "CMP r1, #0");
  val thms = arm_spec (enc "B -#12");
  val thms = arm_spec (enc "ADD r5, pc, #4096");
  val thms = arm_spec (enc "ADD r6, pc, #4096");
  val thms = arm_spec (enc "SUBCS r1, r1, #10");
  val thms = arm_spec (enc "ADDNE r0, r0, #1");
  val thms = arm_spec (enc "BNE -#12");
  val thms = arm_spec (enc "MOVGT r2, #5");
  val thms = arm_spec (enc "LDRNE r1, [r1]");
  val thms = arm_spec (enc "LDRBNE r2, [r3]");
  val thms = arm_spec (enc "BNE +#420");
  val thms = arm_spec (enc "LDRLS r2, [r11, #-40]");
  val thms = arm_spec (enc "SUBLS r2, r2, #1");
  val thms = arm_spec (enc "SUBLS r11, r11, #4");
  val thms = arm_spec (enc "MOVGT r12, r0");
  val thms = arm_spec (enc "ADD r0, pc, #16");
  val thms = arm_spec (enc "SUB r0, pc, #60");
  val thms = arm_spec (enc "SUBLS r2, r2, #1");
  val thms = arm_spec (enc "SUBLS r11, r11, #4");
  val thms = arm_spec (enc "LDRGT r0, [r11, #-44]");
  val thms = arm_spec (enc "MOVGT r1, r3");
  val thms = arm_spec (enc "MOVGT r12, r5");
  val thms = arm_spec (enc "MOVGT r1, r6");
  val thms = arm_spec (enc "MOVGT r0, r6");
  val thms = arm_spec (enc "STRB r2, [r3]");
  val thms = arm_spec (enc "STMIA r4, {r5-r10}");
  val thms = arm_spec (enc "LDMIA r4, {r5-r10}");
  val thms = arm_spec (enc "STRB r2, [r1], #1");
  val thms = arm_spec (enc "STRB r3, [r1], #1");
  val thms = arm_spec (enc "STMIB r8!, {r14}");
  val thms = arm_spec (enc "STMIB r8!, {r0, r14}");
  val thms = arm_spec (enc "STMDB sp!, {r0-r2, r15}");
  val thms = arm_spec (enc "LDRB r2, [r3]");
  val thms = arm_spec (enc "STRB r2, [r3]");
  val thms = arm_spec (enc "SWPB r2, r4, [r3,]");
  val thms = arm_spec (enc "LDR r2, [r3,#12]");
  val thms = arm_spec (enc "STR r2, [r3,#12]");
  val thms = arm_spec (enc "SWP r2, r4, [r3]");
  val thms = arm_spec (enc "LDRH r2, [r3]");
  val thms = arm_spec (enc "STRH r2, [r3]");
  val thms = arm_spec (enc "LDR r0, [r11, #-8]");
  val thms = arm_spec (enc "LDR r0, [r11]");
  val thms = arm_spec (enc "STR r0, [r11, #-8]");
  val thms = arm_spec (enc "BX lr");
  val thms = arm_spec (enc "BLX r2");
  val thms = arm_spec (enc "LDR pc, [r8]");
  val thms = arm_spec (enc "LDRLS pc, [r8], #-4");
  val thms = arm_spec (enc "LDMIA sp!, {r0-r2, r15}");
  val thms = arm_spec (enc "LDR r0, [pc, #308]");
  val thms = arm_spec (enc "LDR r0, [pc, #4056]");
  val thms = arm_spec (enc "LDR r8, [pc, #3988]");
  val thms = arm_spec (enc "LDR r2, [pc, #3984]");
  val thms = arm_spec (enc "LDR r12, [pc, #3880]");
  val thms = arm_spec (enc "LDR r12, [pc, #3856]");
  val thms = arm_spec (enc "LDR r1, [pc, #1020]");
  val thms = arm_spec (enc "LDR r1, [pc, #-20]");

*)

end
