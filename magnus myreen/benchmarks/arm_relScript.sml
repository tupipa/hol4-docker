
open HolKernel Parse boolLib bossLib; val _ = new_theory "arm_rel";

open armTheory armLib arm_stepTheory pred_setTheory pairTheory optionTheory;
open arithmeticTheory wordsTheory wordsLib addressTheory combinTheory pairSyntax;
open sumTheory whileTheory;

infix \\
val op \\ = op THEN;

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE


(* we define a total-correctness machine-code Hoare triple *)

val TRIPLE_def = Define `
  TRIPLE (assert,next) pre code post =
    !state c.
      assert (code UNION c,pre) state ==>
      ?n. assert (code UNION c,post) (FUNPOW next n state)`;


(* theorems about this Hoare triple *)

val TRIPLE_COMPOSE = store_thm("TRIPLE_COMPOSE",
  ``!i p c m q. TRIPLE i p c m /\ TRIPLE i m c q ==> TRIPLE i p c q``,
  SIMP_TAC std_ss [TRIPLE_def,FORALL_PROD] THEN REPEAT STRIP_TAC
  THEN METIS_TAC [FUNPOW_ADD]);

val TRIPLE_EXTEND = store_thm("TRIPLE_EXTEND",
  ``!i p c q c'. TRIPLE i p c q ==> c SUBSET c' ==> TRIPLE i p c' q``,
  SIMP_TAC std_ss [TRIPLE_def,FORALL_PROD] THEN REPEAT STRIP_TAC
  \\ `c' UNION c'' = c UNION (c' UNION c'')` by FULL_SIMP_TAC std_ss [EXTENSION,IN_UNION,SUBSET_DEF]
  THEN1 (REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ METIS_TAC []);

val TRIPLE_REFL = store_thm("TRIPLE_REFL",
  ``!i c p. TRIPLE i p c p``,
  SIMP_TAC std_ss [FORALL_PROD,TRIPLE_def] \\ METIS_TAC [FUNPOW]);

val TRIPLE_COMPOSE_ALT = store_thm("TRIPLE_COMPOSE_ALT",
  ``!i p c m q. TRIPLE i m c q ==> TRIPLE i p c m ==> TRIPLE i p c q``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC TRIPLE_COMPOSE
  \\ Q.EXISTS_TAC `m` \\ FULL_SIMP_TAC std_ss []);

val COND_MERGE = store_thm("COND_MERGE",
  ``(x1 ==> f (g x2)) /\ (~x1 ==> f (g y2)) ==>
    f (g (if x1 then x2 else y2))``,
  Cases_on `x1` \\ FULL_SIMP_TAC std_ss []);

val TERM_TAILREC_def = Define `
  TERM_TAILREC f g (d:'a -> bool # 'b) x =
    let (cond,y) = d (WHILE g f x) in
      (cond /\ (?n. ~g (FUNPOW f n x)),y)`;

val SHORT_TERM_TAILREC_def = Define `
  SHORT_TERM_TAILREC (f:'a -> 'a + (bool # 'b)) =
    TERM_TAILREC (OUTL o f) (ISL o f) (OUTR o f)`;

val TERM_TAILREC_THM = store_thm("TERM_TAILREC_THM",
  ``TERM_TAILREC f g d x = if g x then TERM_TAILREC f g d (f x) else d x``,
  REVERSE (Cases_on `g x`) \\ FULL_SIMP_TAC std_ss [TERM_TAILREC_def,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [Once WHILE] THEN1
   (Cases_on `d x` \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC std_ss [FUNPOW])
  \\ Cases_on `(d (WHILE g f (f x)))` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `n` \\ FULL_SIMP_TAC std_ss [FUNPOW] \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `SUC n` \\ FULL_SIMP_TAC std_ss [FUNPOW]);

val TRIPLE_TERM_TAILREC = prove(
  ``(!c x state. (FST i) (c,post (F,x)) state) ==>
    (!x. TRIPLE i (pre x) c (if g x then pre (f x) else post (d x))) ==>
    (!x. TRIPLE i (pre x) c (post (TERM_TAILREC f g d x)))``,
  Cases_on `i` \\ SIMP_TAC std_ss [TERM_TAILREC_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ REVERSE (Cases_on `?n. ~g (FUNPOW f n x)`) THEN1
   (FULL_SIMP_TAC std_ss [] \\ Cases_on `d (WHILE g f x)`
    \\ FULL_SIMP_TAC std_ss [TRIPLE_def])
  \\ Q.PAT_ASSUM `!c x. bbb` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`x`,`x`)
  \\ Induct_on `n` \\ FULL_SIMP_TAC std_ss [FUNPOW] \\ REPEAT STRIP_TAC THEN1
   (Q.PAT_ASSUM `!x.bbb` (MP_TAC o Q.SPEC `x`)
    \\ ONCE_REWRITE_TAC [WHILE] \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `d x` \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE (`q' /\ (?n. ~g (FUNPOW f n x)) = q'` by ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `q'` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC std_ss [FUNPOW])
  \\ REPEAT STRIP_TAC \\ REVERSE (Cases_on `g x`) THEN1
   (POP_ASSUM (MP_TAC) \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
    \\ Q.PAT_ASSUM `!x.bbb` (MP_TAC o Q.SPEC `x`)
    \\ ONCE_REWRITE_TAC [WHILE] \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `d x` \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE (`q' /\ (?n. ~g (FUNPOW f n x)) = q'` by ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `q'` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC std_ss [FUNPOW])
  \\ MATCH_MP_TAC TRIPLE_COMPOSE
  \\ Q.EXISTS_TAC `pre (f x)` \\ STRIP_TAC THEN1 METIS_TAC []
  \\ RES_TAC \\ ONCE_REWRITE_TAC [WHILE] \\ FULL_SIMP_TAC std_ss []
  \\ `(?n. ~g (FUNPOW f n (f x))) = (?n. ~g (FUNPOW f n x))` by ALL_TAC THEN1
   (REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    THEN1 (Q.EXISTS_TAC `SUC n'` \\ FULL_SIMP_TAC std_ss [FUNPOW])
    \\ Cases_on `n'` \\ FULL_SIMP_TAC std_ss [FUNPOW] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss []);

val my_sum_case_def = Define `
  my_sum_case f1 f2 x = case x of INL y => f1 y | INR y => f2 y`;

val my_sum_case_thm = prove(
  ``!x. my_sum_case pre post x = if ISL x then pre (OUTL x) else post (OUTR x)``,
  Cases \\ SRW_TAC [] [my_sum_case_def]);

val SHORT_TERM_TAILREC = store_thm("SHORT_TERM_TAILREC",
  ``(!x. TRIPLE i (pre x) c (my_sum_case pre post (f x))) ==>
    (!c x state. (FST i) (c,post (F,x)) state) ==>
    (!x. TRIPLE i (pre x) c (post (SHORT_TERM_TAILREC f x)))``,
  SIMP_TAC std_ss [SHORT_TERM_TAILREC_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] TRIPLE_TERM_TAILREC)
  \\ FULL_SIMP_TAC std_ss [my_sum_case_thm]);


(* definition of ARM_ASSERT and ARM_TOTAL_NEXT *)

val _ = Hol_datatype `
  arm_assertion = ARM_ASSERTION of
                    (* pc *) word32 =>
                    (* r0 *) word32 =>
                    (* r1 *) word32 =>
                    (* r2 *) word32 =>
                    (* r3 *) word32 =>
                    (* r4 *) word32 =>
                    (* r5 *) word32 =>
                    (* r6 *) word32 =>
                    (* r7 *) word32 =>
                    (* r8 *) word32 =>
                    (* r9 *) word32 =>
                    (* r10 *) word32 =>
                    (* r11 *) word32 =>
                    (* r12 *) word32 =>
                    (* r13 *) word32 =>
                    (* r14 *) word32 =>
                    (* n *) bool option =>
                    (* z *) bool option =>
                    (* c *) bool option =>
                    (* v *) bool option =>
                    (* domain of memory *) word32 set =>
                    (* memory *) (word32 -> word8)`;

val arm_assert_tm =
  ``ARM_ASSERTION r15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 n z c v dm m``

val option_assert_def = Define `
  (option_assert NONE x = T) /\
  (option_assert (SOME y) x = (x = y))`;

val _ = wordsLib.guess_lengths();

val ARM_READ_MEM32_def = Define `
  ARM_READ_MEM32 a state =
    ARM_READ_MEM (a + 3w) state @@
    ARM_READ_MEM (a + 2w) state @@
    ARM_READ_MEM (a + 1w) state @@
    ARM_READ_MEM (a + 0w) state`;

val ARM_STATE_OK_def = Define `
  ARM_STATE_OK state =
    (ARM_ARCH state = ARMv6) /\ (ARM_EXTENSIONS state = {}) /\
    (ARM_UNALIGNED_SUPPORT state) /\ (ARM_READ_EVENT_REGISTER state) /\
    ~(ARM_READ_INTERRUPT_WAIT state) /\ ~(ARM_READ_SCTLR sctlrV state) /\
    (ARM_READ_SCTLR sctlrA state) /\ ~(ARM_READ_SCTLR sctlrU state) /\
    (ARM_READ_IT state = 0w) /\ ~(ARM_READ_STATUS psrJ state) /\
    ~(ARM_READ_STATUS psrT state) /\ ~(ARM_READ_STATUS psrE state) /\
    (ARM_MODE state = 16w)`;

val ARM_READ_MEM32_IMP_LEMMA = prove(
  ``(ARM_READ_MEM32 a s = w) =
    (ARM_READ_MEM a s = (7 >< 0) w) /\
    (ARM_READ_MEM (a+1w) s = (15 >< 8) w) /\
    (ARM_READ_MEM (a+2w) s = (23 >< 16) w) /\
    (ARM_READ_MEM (a+3w) s = (31 >< 24) w)``,
  SIMP_TAC std_ss [ARM_READ_MEM32_def,WORD_ADD_0] \\ blastLib.BBLAST_TAC);

val ARM_READ_MEM32_IMP =
  ARM_READ_MEM32_IMP_LEMMA
  |> Q.INST [`w`|->`n2w n`]
  |> SIMP_RULE std_ss [EVAL ``((m >< n) ((n2w k):word32)):word8``]
  |> SIMP_RULE std_ss [bitTheory.BITS_THM]

val _ = save_thm("ARM_READ_MEM32_IMP",ARM_READ_MEM32_IMP);

val SET_EVERY_def = Define `
  SET_EVERY s P = !x. x IN s ==> P x`;

val SET_EVERY_THM = store_thm("SET_EVERY_THM",
  ``(SET_EVERY {} P = T) /\
    (SET_EVERY (x INSERT s) P = P x /\ SET_EVERY s P) /\
    (SET_EVERY (s UNION t) P = SET_EVERY s P /\ SET_EVERY t P)``,
  SIMP_TAC std_ss [SET_EVERY_def,IN_INSERT,IN_UNION,NOT_IN_EMPTY] \\ METIS_TAC []);

val ARM_ASSERT_def = Define `
  ARM_ASSERT (code,(^arm_assert_tm,condition)) state =
    condition ==>
      SET_EVERY code ( \ (a,w).
         (ARM_READ_MEM32 a state = w) /\ (a && 3w = 0w) /\
         ~(a IN dm) /\ ~(a+1w IN dm) /\ ~(a+2w IN dm) /\ ~(a+3w IN dm)) /\
      (ARM_READ_REG 15w state = r15) /\
      (ARM_READ_REG 0w state = r0) /\
      (ARM_READ_REG 1w state = r1) /\
      (ARM_READ_REG 2w state = r2) /\
      (ARM_READ_REG 3w state = r3) /\
      (ARM_READ_REG 4w state = r4) /\
      (ARM_READ_REG 5w state = r5) /\
      (ARM_READ_REG 6w state = r6) /\
      (ARM_READ_REG 7w state = r7) /\
      (ARM_READ_REG 8w state = r8) /\
      (ARM_READ_REG 9w state = r9) /\
      (ARM_READ_REG 10w state = r10) /\
      (ARM_READ_REG 11w state = r11) /\
      (ARM_READ_REG 12w state = r12) /\
      (ARM_READ_REG 13w state = r13) /\
      (ARM_READ_REG 14w state = r14) /\
      option_assert n (ARM_READ_STATUS psrN state) /\
      option_assert z (ARM_READ_STATUS psrZ state) /\
      option_assert c (ARM_READ_STATUS psrC state) /\
      option_assert v (ARM_READ_STATUS psrV state) /\
      SET_EVERY dm (\a. ARM_READ_MEM a state = m a) /\
      ARM_STATE_OK state`

val ARM_TOTAL_NEXT_def = Define `
  ARM_TOTAL_NEXT = THE o ARM_NEXT NoInterrupt`;

val ARM_def = Define `ARM = (ARM_ASSERT,ARM_TOTAL_NEXT)`;

val IMP_ARM_TRIPLE = store_thm("IMP_ARM_TRIPLE",
  ``(!s e. ARM_ASSERT (code UNION e,pre) s /\ c ==>
           ?s2. (ARM_NEXT NoInterrupt s = SOME s2) /\
                ARM_ASSERT (code UNION e,post,c) s2) ==>
    TRIPLE ARM (pre) code (post,c)``,
  REVERSE (Cases_on `c`)
  THEN1 (Cases_on `post` \\ FULL_SIMP_TAC std_ss [TRIPLE_def,ARM_def,ARM_ASSERT_def])
  \\ SIMP_TAC std_ss [TRIPLE_def,ARM_def] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Q.EXISTS_TAC `SUC 0` \\ FULL_SIMP_TAC std_ss [FUNPOW,ARM_TOTAL_NEXT_def]);


(* misc. lemmas used in the automation (arm_relLib) *)

val ADD_WITH_CARRY_SUB_n2w = save_thm("ADD_WITH_CARRY_SUB_n2w",
  ((RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
    (ONCE_REWRITE_CONV [GSYM WORD_NOT_NOT] THENC
     ONCE_REWRITE_CONV [word_1comp_n2w] THENC
     SIMP_CONV (std_ss++wordsLib.SIZES_ss) []) THENC
   REWRITE_CONV [ADD_WITH_CARRY_SUB])
      ``add_with_carry (x:word32,n2w n,T)``);

val aligned4_thm = store_thm("aligned4_thm",
  ``!a. aligned (a,4) = ALIGNED a``,
  Cases \\ ASM_SIMP_TAC std_ss [arm_coretypesTheory.aligned_def,
      arm_coretypesTheory.align_def,w2n_n2w,ALIGNED_n2w,n2w_11]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ (STRIP_ASSUME_TAC o Q.SPEC `n` o GSYM o
      RW1 [arithmeticTheory.MULT_COMM] o MATCH_MP arithmeticTheory.DIVISION) (DECIDE ``0 < 4:num``)
  \\ Cases_on `n MOD 4 = 0` \\ FULL_SIMP_TAC std_ss []
  \\ `(4 * (n DIV 4)) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val aligned2_thm = store_thm("aligned2_thm",
  ``!a:word32. aligned (a,2) = (a && 1w = 0w)``,
  Cases \\ ASM_SIMP_TAC std_ss [arm_coretypesTheory.aligned_def,
      arm_coretypesTheory.align_def,w2n_n2w,n2w_and_1,n2w_11]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ (STRIP_ASSUME_TAC o Q.SPEC `n` o GSYM o
      RW1 [arithmeticTheory.MULT_COMM] o MATCH_MP arithmeticTheory.DIVISION) (DECIDE ``0 < 2:num``)
  \\ Cases_on `n MOD 2 = 0` \\ FULL_SIMP_TAC std_ss []
  \\ `(2 * (n DIV 2)) < 4294967296` by DECIDE_TAC
  \\ `0 < 2:num` by DECIDE_TAC
  \\ `n MOD 2 < 2` by METIS_TAC [arithmeticTheory.MOD_LESS]
  \\ `n MOD 2 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ DECIDE_TAC);

val aligned_bx_lemma = store_thm("aligned_bx_lemma",
  ``!w:word32. aligned (w,4) ==> aligned_bx w /\ ~(w ' 0)``,
  SIMP_TAC std_ss [aligned4_thm,ALIGNED_BITS,arm_stepTheory.aligned_bx_thm]);

val ARM_WRITE_STATUS_T_IGNORE_UPDATE = store_thm("ARM_WRITE_STATUS_T_IGNORE_UPDATE",
  ``(~ARM_READ_STATUS psrT s ==> (ARM_WRITE_STATUS psrT F s = s)) /\
    (ARM_WRITE_STATUS psrT b (ARM_WRITE_REG r w s) =
     ARM_WRITE_REG r w (ARM_WRITE_STATUS psrT b s))``,
  EVAL_TAC \\ SRW_TAC [] [FUN_EQ_THM,APPLY_UPDATE_THM,
    arm_seq_monadTheory.arm_state_component_equality,
    arm_coretypesTheory.ARMpsr_component_equality] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC std_ss []);

val ARM_WRITE_STS_def = Define `
  ARM_WRITE_STS a x s = if a IN {psrN;psrZ;psrC;psrV;psrQ} then ARM_WRITE_STATUS a x s else s`;

val ARM_WRITE_STS_INTRO = store_thm("ARM_WRITE_STS_INTRO",
  ``(ARM_WRITE_STATUS psrN x s = ARM_WRITE_STS psrN x s) /\
    (ARM_WRITE_STATUS psrZ x s = ARM_WRITE_STS psrZ x s) /\
    (ARM_WRITE_STATUS psrC x s = ARM_WRITE_STS psrC x s) /\
    (ARM_WRITE_STATUS psrV x s = ARM_WRITE_STS psrV x s) /\
    (ARM_WRITE_STATUS psrQ x s = ARM_WRITE_STS psrQ x s)``,
  SIMP_TAC std_ss [ARM_WRITE_STS_def,IN_INSERT]);

val ARM_STATE_OK_OF_UPDATES = prove(
  ``(!a x. ARM_STATE_OK (ARM_WRITE_REG a x s) = ARM_STATE_OK s) /\
    (!a x. ARM_STATE_OK (ARM_WRITE_MEM a x s) = ARM_STATE_OK s) /\
    (!a x. ARM_STATE_OK (ARM_WRITE_STS a x s) = ARM_STATE_OK s) /\
    (!a x. ARM_STATE_OK (ARM_WRITE_MEM_WRITE a x s) = ARM_STATE_OK s) /\
    (!a. ARM_STATE_OK (ARM_WRITE_MEM_READ a s) = ARM_STATE_OK s) /\
    (!a x y. ARM_STATE_OK (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) = ARM_STATE_OK s)``,
  SIMP_TAC std_ss [ARM_STATE_OK_def] \\ REPEAT STRIP_TAC
  \\ EVAL_TAC \\ SRW_TAC [] [] \\ EVAL_TAC);

val ARM_READ_WRITE = LIST_CONJ [REG_OF_UPDATES,MEM_OF_UPDATES,CPSR_COMPONENTS_OF_UPDATES,ARM_STATE_OK_OF_UPDATES]
val _ = save_thm("ARM_READ_WRITE",ARM_READ_WRITE);

val TRIPLE_FRAME_BOOL = store_thm("TRIPLE_FRAME_BOOL",
  ``TRIPLE ARM (pre,c1) code (post,c2) ==>
    !c. TRIPLE ARM (pre,c /\ c1) code (post,c /\ c2)``,
  SIMP_TAC std_ss [TRIPLE_def,ARM_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `c` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `post` \\ FULL_SIMP_TAC std_ss [ARM_ASSERT_def]);


val _ = export_theory();
