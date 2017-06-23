
open HolKernel Parse boolLib bossLib;

val _ = new_theory "benchmarks";

open armTheory armLib arm_stepTheory pred_setTheory pairTheory optionTheory;
open arithmeticTheory wordsTheory wordsLib addressTheory combinTheory pairSyntax;
open sumTheory whileTheory;

open rel_decompilerLib;


(* Infrastructure for making measurements --------------------------------------- *)

fun model_evaluator f (name:string) qcode = let
  fun eval_inst hex = 
    if String.isPrefix "insert:" hex then () else (f hex; ())    
  val _ = map eval_inst (quote_to_strings qcode)
  in ([TRUTH],TRUTH) end;

val (old_arm_spec,_,_,_) = prog_armLib.arm_tools_no_status

val new_model = model_evaluator arm_relLib.arm_spec
val old_model = model_evaluator old_arm_spec

fun measure_it f x = let
  (* measure inferences *)
  val _ = Count.counting_thms true
  val _ = Count.reset_thm_count ()
  val start1 = Time.now()
  val _ = f x
  val end1 = Time.now()
  val total1 = Count.thm_count ()  
  val _ = Count.counting_thms false
  val time1 = Time.toReal ((op Time.-)(end1,start1))
  in (Real.fromInt (#total total1),time1) end;

fun compare_it (* new *) f1 x1 (* old *) f2 x2 = let
  val _ = PolyML.fullGC()
  val (total1,time1) = measure_it f1 x1
  val (total2,time2) = measure_it f2 x2
  val time_reduction = (1.0 - time1 / time2) * 100.0
  val prim_reduction = (1.0 - total1 / total2) * 100.0
  (* print results *)
  val _ = print "\n  Comparison between old and new:\n\n"
  val _ = print ("    inferences:  " ^ int_to_string (Real.toInt IEEEReal.TO_NEAREST total2) ^ " (old), "
                                     ^ int_to_string (Real.toInt IEEEReal.TO_NEAREST total1) ^ " (new), "
                                     ^ Real.toString prim_reduction ^ " %\n")
  val _ = print ("    time:        " ^ Real.toString time2 ^ " s (old), "
                                     ^ Real.toString time1 ^ " s (new), "
                                     ^ Real.toString time_reduction ^ " %\n\n")
  in () end  

fun measure_model f1 x1 = let
  val _ = PolyML.fullGC()
  val (total1,time1) = measure_it f1 x1
  (* print results *)
  val _ = print "\n  Model evaluation:\n\n"
  val _ = print ("    inferences:  " ^ int_to_string (Real.toInt IEEEReal.TO_NEAREST total1) ^ " \n")
  val _ = print ("    time:        "       ^ Real.toString time1 ^ " s \n\n")
  in () end; 

fun old_decompile name qcode = let
  val (x,y) = decompilerLib.decompile prog_armLib.arm_tools_no_status name qcode
  in ([x],y) end

fun benchmark name test = let
  val _ = helperLib.set_echo 0
  val _ = print ("\n======================================================================================\n\n")
  val _ = print ("  Benchmark name: " ^ name ^ "\n")
  val _ = measure_model test new_model 
  val _ = test old_model
  val _ = compare_it test fast_decompile test old_decompile
  val _ = helperLib.set_echo 3
  in () end;


(* Benchmarks ------------------------------------------------------------------- *)

fun do_sum f = let

val name = "sum"
val qcode = `
  E7921003  (* L: ldr r1,[r2,r3]  *)
  E0800001  (*    add r0,r1       *)
  E2533004  (*    subs r3,#4      *) 
  1AFFFFFB  (*    bne L           *)` : term quotation;

in f name qcode end

val _ = benchmark "sum of array" do_sum

(*
val _ = compare_it do_sum fast_decompile do_sum old_decompile;
*)


(* This is commented out because it's not part of our benchmarks.

fun do_list f = let

val name = "length"
val qcode = `
  E3A00000  (*    mov r0,#0       *)
  E3510000  (* L: cmp r1,#0       *)
  12800001  (*    addne r0,r0,#1  *)
  15911000  (*    ldrne r1,[r1]   *)
  1AFFFFFB  (*    bne L           *)` : term quotation;

in f name qcode end

val _ = benchmark "length of linked list" do_list

(*
val _ = compare_it do_list fast_decompile do_list old_decompile;
*)

*)


fun do_gc f = let

val _ = f "arm_move" `
  E3550000 (* cmp r5,#0 *)
  0A000009 (* beq L1 *)
  E5957000 (* ldr r7,[r5] *)
  E3170001 (* tst r7,#1 *)
  04847004 (* streq r7,[r4],#4 *)
  05958004 (* ldreq r8,[r5,#4] *)
  05957008 (* ldreq r7,[r5,#8] *)
  04848004 (* streq r8,[r4],#4 *)
  04847004 (* streq r7,[r4],#4 *)
  0244700B (* subeq r7,r4,#11 *)
  05857000 (* streq r7,[r5] *)
  E2475001 (* sub r5,r7,#1 *)`;

val _ = f "arm_move2" `
  E3560000 (* cmp r6,#0 *)
  0A000009 (* beq L2 *)
  E5967000 (* ldr r7,[r6] *)
  E3170001 (* tst r7,#1 *)
  04847004 (* streq r7,[r4],#4 *)
  05968004 (* ldreq r8,[r6,#4] *)
  05967008 (* ldreq r7,[r6,#8] *)
  04848004 (* streq r8,[r4],#4 *)
  04847004 (* streq r7,[r4],#4 *)
  0244700B (* subeq r7,r4,#11 *)
  05867000 (* streq r7,[r6] *)
  E2476001 (* sub r6,r7,#1 *)`;

val _ = f "arm_cheney_step" `
  E5935000 (* ldr r5,[r3] *)
  E5936004 (* ldr r6,[r3,#4] *)
  insert: arm_move
  insert: arm_move2
  E4835004 (* L2:str r5,[r3],#4 *)
  E4836004 (* str r6,[r3],#4 *)
  E2833004 (* add r3,r3,#4 *)`;

val _ = f "arm_cheney_loop" `
  E1530004 (* CHENEY:cmp r3,r4 *)
  0A00001D (* beq EXIT *)
  insert: arm_cheney_step
  EAFFFFDF (* b CHENEY *)`;

val _ = f "arm_move_roots" `
  E3560000 (* ROOTS:cmp r6,#0 *)
  0A00000F (* beq CHENEY *)
  E5995000 (* ldr r5,[r9] *)
  insert: arm_move
  E2466001 (* RL:sub r6,r6,#1 *)
  E4895004 (* str r5,[r9],#4 *)
  EAFFFFED (* b ROOTS *)`;

val _ = f "arm_c_init" `
  E2355001 (* eors r5,r5,#1 *)    (* calc u *)
  E289300C (* add r3,r9,#12 *)    (* set i *)
  00833006 (* addeq r3,r3,r6 *)`;

val _ = f "arm_collect" `
  E519501C (* ldr r5,[r9,#-28] *)
  E5196020 (* ldr r6,[r9,#-32] *)
  insert: arm_c_init
  E509501C (* str r5,[r9,#-28] *)
  E0835006 (* add r5,r3,r6 *)
  E1A04003 (* mov r4,r3 *)
  E5895004 (* str r5,[r9,#4] *)
  E3A06006 (* mov r6,#6 *)
  E2499018 (* sub r9,r9,#24 *)
  insert: arm_move_roots
  insert: arm_cheney_loop  (* main loop *)
  E5994004 (* EXIT:ldr r4,[r9,#4] *)`;

val _ = f "arm_alloc_gc" `
  E1530004 (* cmp r3,r4 *)
  1A00003D (* bne NO_GC *)
  insert: arm_collect`;

val _ = f "arm_alloc_aux" `
  E5197018 (* NO_GC:ldr r7,[r9,#-24] *)
  E5198014 (* ldr r8,[r9,#-20] *)
  E3A06000 (* mov r6,#0 *)
  E1530004 (* cmp r3,r4 *)
  15093018 (* strne r3,[r9,#-24] *)
  14837004 (* strne r7,[r3],#4 *)
  14838004 (* strne r8,[r3],#4 *)
  14836004 (* strne r6,[r3],#4 *)
  03A07000 (* moveq r7,#0 *)
  05097018 (* streq r7,[r9,#-24] *)
  E5893000 (* str r3,[r9] *)`;

val _ = f "arm_alloc_mem" `
  E5993000 (* ldr r3,[r9] *)
  E5994004 (* ldr r4,[r9,#4] *)
  insert: arm_alloc_gc
  insert: arm_alloc_aux`;

val _ = f "arm_alloc" `
  E5093018 (* str r3,[r9,#-24] *)
  E5094014 (* str r4,[r9,#-20] *)
  E5095010 (* str r5,[r9,#-16] *)
  E509600C (* str r6,[r9,#-12] *)
  E5097008 (* str r7,[r9,#-8] *)
  E5098004 (* str r8,[r9,#-4] *)
  insert: arm_alloc_mem
  E5193018 (* ldr r3,[r9,#-24] *)
  E5194014 (* ldr r4,[r9,#-20] *)
  E5195010 (* ldr r5,[r9,#-16] *)
  E519600C (* ldr r6,[r9,#-12] *)
  E5197008 (* ldr r7,[r9,#-8] *)
  E5198004 (* ldr r8,[r9,#-4] *)`;

in () end;

val _ = benchmark "copying garbage collector" do_gc;

(*
val _ = compare_it do_gc fast_decompile do_gc old_decompile;
*)


fun do_1024_bit_add f = let

val _ = f "add1024_step" `
  E8B103C0    (*     ldm r1!,{r6,r7,r8,r9}      *)
  E8B0003C    (*     ldm r0!,{r2,r3,r4,r5}      *)
  E0B22006    (*     adcs r2,r6                 *)
  E0B33007    (*     adcs r3,r7                 *)
  E0B44008    (*     adcs r4,r8                 *)
  E0B55009    (*     adcs r5,r9                 *)
  E8AA003C    (*     stm r10!,{r2,r3,r4,r5}     *)`;

val _ = f "add1024_step8" `
  insert: add1024_step
  insert: add1024_step
  insert: add1024_step
  insert: add1024_step
  insert: add1024_step
  insert: add1024_step
  insert: add1024_step
  insert: add1024_step`;

val _ = f "add1024" `
  insert: add1024_step8
  insert: add1024_step8
  insert: add1024_step8
  insert: add1024_step8`;

in () end;

val _ = benchmark "1024-bit multiword addition" do_1024_bit_add;

(*
val _ = compare_it do_1024_bit_add fast_decompile do_1024_bit_add old_decompile;
*)


fun do_skein f = let

val skein_qcode = `
   115a4:	e59dc04c 	ldr	ip, [sp, #76]	; 0x4c
   115a8:	e58da030 	str	sl, [sp, #48]	; 0x30
   115ac:	e58db034 	str	fp, [sp, #52]	; 0x34
   115b0:	e098800c 	adds	r8, r8, ip
   115b4:	e58d8028 	str	r8, [sp, #40]	; 0x28
   115b8:	e2a99000 	adc	r9, r9, #0
   115bc:	e58d902c 	str	r9, [sp, #44]	; 0x2c
   115c0:	e028800a 	eor	r8, r8, sl
   115c4:	e029900b 	eor	r9, r9, fp
   115c8:	e58d8038 	str	r8, [sp, #56]	; 0x38
   115cc:	e58d903c 	str	r9, [sp, #60]	; 0x3c
   115d0:	e0208002 	eor	r8, r0, r2
   115d4:	e0219003 	eor	r9, r1, r3
   115d8:	e0288004 	eor	r8, r8, r4
   115dc:	e2800000 	add	r0, r0, #0  ; hack
   115e0:	e28dc000 	add	ip, sp, #0
   115e4:	e2800000 	add	r0, r0, #0  ; hack
   115e8:	e0299005 	eor	r9, r9, r5
   115ec:	e0288006 	eor	r8, r8, r6
   115f0:	e0299007 	eor	r9, r9, r7
   115f4:	e028800a 	eor	r8, r8, sl
   115f8:	e029900b 	eor	r9, r9, fp
   115fc:	e59db044 	ldr	fp, [sp, #68]	; 0x44
   11600:	e88c03ff 	stm	ip, {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9}
   11604:	e1a0c00b 	mov	ip, fp
   11608:	e59b8000 	ldr	r8, [fp]
   1160c:	e59b9004 	ldr	r9, [fp, #4]
   11610:	e59ba008 	ldr	sl, [fp, #8]
   11614:	e0900008 	adds	r0, r0, r8
   11618:	e59bb00c 	ldr	fp, [fp, #12]
   1161c:	e0a11009 	adc	r1, r1, r9
   11620:	e59c8010 	ldr	r8, [ip, #16]
   11624:	e092200a 	adds	r2, r2, sl
   11628:	e59c9014 	ldr	r9, [ip, #20]
   1162c:	e0a3300b 	adc	r3, r3, fp
   11630:	e59ca018 	ldr	sl, [ip, #24]
   11634:	e0944008 	adds	r4, r4, r8
   11638:	e59cb01c 	ldr	fp, [ip, #28]
   1163c:	e0a55009 	adc	r5, r5, r9
   11640:	e59d8028 	ldr	r8, [sp, #40]	; 0x28
   11644:	e096600a 	adds	r6, r6, sl
   11648:	e59d902c 	ldr	r9, [sp, #44]	; 0x2c
   1164c:	e0a7700b 	adc	r7, r7, fp
   11650:	e59da030 	ldr	sl, [sp, #48]	; 0x30
   11654:	e0922008 	adds	r2, r2, r8
   11658:	e59db034 	ldr	fp, [sp, #52]	; 0x34
   1165c:	e0a33009 	adc	r3, r3, r9
   11660:	e094400a 	adds	r4, r4, sl
   11664:	e0a5500b 	adc	r5, r5, fp
   11668:	e0900002 	adds	r0, r0, r2
   1166c:	e0a11003 	adc	r1, r1, r3
   11670:	e0944006 	adds	r4, r4, r6
   11674:	e0218922 	eor	r8, r1, r2, lsr #18
   11678:	e0a55007 	adc	r5, r5, r7
   1167c:	e0202702 	eor	r2, r0, r2, lsl #14
   11680:	e0259826 	eor	r9, r5, r6, lsr #16
   11684:	e0222923 	eor	r2, r2, r3, lsr #18
   11688:	e0246806 	eor	r6, r4, r6, lsl #16
   1168c:	e0283703 	eor	r3, r8, r3, lsl #14
   11690:	e0266827 	eor	r6, r6, r7, lsr #16
   11694:	e0297807 	eor	r7, r9, r7, lsl #16
   11698:	e0944002 	adds	r4, r4, r2
   1169c:	e0a55003 	adc	r5, r5, r3
   116a0:	e0900006 	adds	r0, r0, r6
   116a4:	e0258c82 	eor	r8, r5, r2, lsl #25
   116a8:	e0a11007 	adc	r1, r1, r7
   116ac:	e02423a2 	eor	r2, r4, r2, lsr #7
   116b0:	e0219a06 	eor	r9, r1, r6, lsl #20
   116b4:	e0222c83 	eor	r2, r2, r3, lsl #25
   116b8:	e0206626 	eor	r6, r0, r6, lsr #12
   116bc:	e02833a3 	eor	r3, r8, r3, lsr #7
   116c0:	e0266a07 	eor	r6, r6, r7, lsl #20
   116c4:	e0297627 	eor	r7, r9, r7, lsr #12
   116c8:	e0900002 	adds	r0, r0, r2
   116cc:	e0a11003 	adc	r1, r1, r3
   116d0:	e0944006 	adds	r4, r4, r6
   116d4:	e02184a2 	eor	r8, r1, r2, lsr #9
   116d8:	e0a55007 	adc	r5, r5, r7
   116dc:	e0202b82 	eor	r2, r0, r2, lsl #23
   116e0:	e0259406 	eor	r9, r5, r6, lsl #8
   116e4:	e02224a3 	eor	r2, r2, r3, lsr #9
   116e8:	e0246c26 	eor	r6, r4, r6, lsr #24
   116ec:	e0283b83 	eor	r3, r8, r3, lsl #23
   116f0:	e0266407 	eor	r6, r6, r7, lsl #8
   116f4:	e0297c27 	eor	r7, r9, r7, lsr #24
   116f8:	e0944002 	adds	r4, r4, r2
   116fc:	e0a55003 	adc	r5, r5, r3
   11700:	e0900006 	adds	r0, r0, r6
   11704:	e0258282 	eor	r8, r5, r2, lsl #5
   11708:	e0a11007 	adc	r1, r1, r7
   1170c:	e0242da2 	eor	r2, r4, r2, lsr #27
   11710:	e0219da6 	eor	r9, r1, r6, lsr #27
   11714:	e0222283 	eor	r2, r2, r3, lsl #5
   11718:	e0206286 	eor	r6, r0, r6, lsl #5
   1171c:	e0283da3 	eor	r3, r8, r3, lsr #27
   11720:	e0266da7 	eor	r6, r6, r7, lsr #27
   11724:	e0297287 	eor	r7, r9, r7, lsl #5
   11728:	e59d8008 	ldr	r8, [sp, #8]
   1172c:	e59d900c 	ldr	r9, [sp, #12]
   11730:	e092200a 	adds	r2, r2, sl
   11734:	e59da010 	ldr	sl, [sp, #16]
   11738:	e0a3300b 	adc	r3, r3, fp
   1173c:	e59db014 	ldr	fp, [sp, #20]
   11740:	e0900008 	adds	r0, r0, r8
   11744:	e59d8018 	ldr	r8, [sp, #24]
   11748:	e0a11009 	adc	r1, r1, r9
   1174c:	e59d901c 	ldr	r9, [sp, #28]
   11750:	e092200a 	adds	r2, r2, sl
   11754:	e59da020 	ldr	sl, [sp, #32]
   11758:	e0a3300b 	adc	r3, r3, fp
   1175c:	e59db024 	ldr	fp, [sp, #36]	; 0x24
   11760:	e0944008 	adds	r4, r4, r8
   11764:	e0a55009 	adc	r5, r5, r9
   11768:	e096600a 	adds	r6, r6, sl
   1176c:	e0a7700b 	adc	r7, r7, fp
   11770:	e59da038 	ldr	sl, [sp, #56]	; 0x38
   11774:	e59db03c 	ldr	fp, [sp, #60]	; 0x3c
   11778:	e2966001 	adds	r6, r6, #1
   1177c:	e2a77000 	adc	r7, r7, #0
   11780:	e094400a 	adds	r4, r4, sl
   11784:	e0a5500b 	adc	r5, r5, fp
   11788:	e0900002 	adds	r0, r0, r2
   1178c:	e0a11003 	adc	r1, r1, r3
   11790:	e0944006 	adds	r4, r4, r6
   11794:	e02183a2 	eor	r8, r1, r2, lsr #7
   11798:	e0a55007 	adc	r5, r5, r7
   1179c:	e0202c82 	eor	r2, r0, r2, lsl #25
   117a0:	e0259086 	eor	r9, r5, r6, lsl #1
   117a4:	e02223a3 	eor	r2, r2, r3, lsr #7
   117a8:	e0246fa6 	eor	r6, r4, r6, lsr #31
   117ac:	e0283c83 	eor	r3, r8, r3, lsl #25
   117b0:	e0266087 	eor	r6, r6, r7, lsl #1
   117b4:	e0297fa7 	eor	r7, r9, r7, lsr #31
   117b8:	e0944002 	adds	r4, r4, r2
   117bc:	e0a55003 	adc	r5, r5, r3
   117c0:	e0900006 	adds	r0, r0, r6
   117c4:	e0258a22 	eor	r8, r5, r2, lsr #20
   117c8:	e0a11007 	adc	r1, r1, r7
   117cc:	e0242602 	eor	r2, r4, r2, lsl #12
   117d0:	e0219706 	eor	r9, r1, r6, lsl #14
   117d4:	e0222a23 	eor	r2, r2, r3, lsr #20
   117d8:	e0206926 	eor	r6, r0, r6, lsr #18
   117dc:	e0283603 	eor	r3, r8, r3, lsl #12
   117e0:	e0266707 	eor	r6, r6, r7, lsl #14
   117e4:	e0297927 	eor	r7, r9, r7, lsr #18
   117e8:	e0900002 	adds	r0, r0, r2
   117ec:	e0a11003 	adc	r1, r1, r3
   117f0:	e0944006 	adds	r4, r4, r6
   117f4:	e0218d02 	eor	r8, r1, r2, lsl #26
   117f8:	e0a55007 	adc	r5, r5, r7
   117fc:	e0202322 	eor	r2, r0, r2, lsr #6
   11800:	e0259526 	eor	r9, r5, r6, lsr #10
   11804:	e0222d03 	eor	r2, r2, r3, lsl #26
   11808:	e0246b06 	eor	r6, r4, r6, lsl #22
   1180c:	e0283323 	eor	r3, r8, r3, lsr #6
   11810:	e0266527 	eor	r6, r6, r7, lsr #10
   11814:	e0297b07 	eor	r7, r9, r7, lsl #22
   11818:	e0944002 	adds	r4, r4, r2
   1181c:	e0a55003 	adc	r5, r5, r3
   11820:	e0900006 	adds	r0, r0, r6
   11824:	e0248003 	eor	r8, r4, r3
   11828:	e0a11007 	adc	r1, r1, r7
   1182c:	e0223005 	eor	r3, r2, r5
   11830:	e0209007 	eor	r9, r0, r7
   11834:	e1a02008 	mov	r2, r8
   11838:	e0267001 	eor	r7, r6, r1
   1183c:	e1a06009 	mov	r6, r9
   11840:	e59d8010 	ldr	r8, [sp, #16]
   11844:	e59d9014 	ldr	r9, [sp, #20]
   11848:	e092200a 	adds	r2, r2, sl
   1184c:	e59da018 	ldr	sl, [sp, #24]
   11850:	e0a3300b 	adc	r3, r3, fp
   11854:	e59db01c 	ldr	fp, [sp, #28]
   11858:	e0900008 	adds	r0, r0, r8
   1185c:	e59d8020 	ldr	r8, [sp, #32]
   11860:	e0a11009 	adc	r1, r1, r9
   11864:	e59d9024 	ldr	r9, [sp, #36]	; 0x24
   11868:	e092200a 	adds	r2, r2, sl
   1186c:	e59da000 	ldr	sl, [sp]
   11870:	e0a3300b 	adc	r3, r3, fp
   11874:	e59db004 	ldr	fp, [sp, #4]
   11878:	e0944008 	adds	r4, r4, r8
   1187c:	e0a55009 	adc	r5, r5, r9
   11880:	e096600a 	adds	r6, r6, sl
   11884:	e0a7700b 	adc	r7, r7, fp
   11888:	e59da028 	ldr	sl, [sp, #40]	; 0x28
   1188c:	e59db02c 	ldr	fp, [sp, #44]	; 0x2c
   11890:	e2966002 	adds	r6, r6, #2
   11894:	e2a77000 	adc	r7, r7, #0
   11898:	e094400a 	adds	r4, r4, sl
   1189c:	e0a5500b 	adc	r5, r5, fp
   118a0:	e0900002 	adds	r0, r0, r2
   118a4:	e0a11003 	adc	r1, r1, r3
   118a8:	e0944006 	adds	r4, r4, r6
   118ac:	e0218922 	eor	r8, r1, r2, lsr #18
   118b0:	e0a55007 	adc	r5, r5, r7
   118b4:	e0202702 	eor	r2, r0, r2, lsl #14
   118b8:	e0259826 	eor	r9, r5, r6, lsr #16
   118bc:	e0222923 	eor	r2, r2, r3, lsr #18
   118c0:	e0246806 	eor	r6, r4, r6, lsl #16
   118c4:	e0283703 	eor	r3, r8, r3, lsl #14
   118c8:	e0266827 	eor	r6, r6, r7, lsr #16
   118cc:	e0297807 	eor	r7, r9, r7, lsl #16
   118d0:	e0944002 	adds	r4, r4, r2
   118d4:	e0a55003 	adc	r5, r5, r3
   118d8:	e0900006 	adds	r0, r0, r6
   118dc:	e0258c82 	eor	r8, r5, r2, lsl #25
   118e0:	e0a11007 	adc	r1, r1, r7
   118e4:	e02423a2 	eor	r2, r4, r2, lsr #7
   118e8:	e0219a06 	eor	r9, r1, r6, lsl #20
   118ec:	e0222c83 	eor	r2, r2, r3, lsl #25
   118f0:	e0206626 	eor	r6, r0, r6, lsr #12
   118f4:	e02833a3 	eor	r3, r8, r3, lsr #7
   118f8:	e0266a07 	eor	r6, r6, r7, lsl #20
   118fc:	e0297627 	eor	r7, r9, r7, lsr #12
   11900:	e0900002 	adds	r0, r0, r2
   11904:	e0a11003 	adc	r1, r1, r3
   11908:	e0944006 	adds	r4, r4, r6
   1190c:	e02184a2 	eor	r8, r1, r2, lsr #9
   11910:	e0a55007 	adc	r5, r5, r7
   11914:	e0202b82 	eor	r2, r0, r2, lsl #23
   11918:	e0259406 	eor	r9, r5, r6, lsl #8
   1191c:	e02224a3 	eor	r2, r2, r3, lsr #9
   11920:	e0246c26 	eor	r6, r4, r6, lsr #24
   11924:	e0283b83 	eor	r3, r8, r3, lsl #23
   11928:	e0266407 	eor	r6, r6, r7, lsl #8
   1192c:	e0297c27 	eor	r7, r9, r7, lsr #24
   11930:	e0944002 	adds	r4, r4, r2
   11934:	e0a55003 	adc	r5, r5, r3
   11938:	e0900006 	adds	r0, r0, r6
   1193c:	e0258282 	eor	r8, r5, r2, lsl #5
   11940:	e0a11007 	adc	r1, r1, r7
   11944:	e0242da2 	eor	r2, r4, r2, lsr #27
   11948:	e0219da6 	eor	r9, r1, r6, lsr #27
   1194c:	e0222283 	eor	r2, r2, r3, lsl #5
   11950:	e0206286 	eor	r6, r0, r6, lsl #5
   11954:	e0283da3 	eor	r3, r8, r3, lsr #27
   11958:	e0266da7 	eor	r6, r6, r7, lsr #27
   1195c:	e0297287 	eor	r7, r9, r7, lsl #5
   11960:	e59d8018 	ldr	r8, [sp, #24]
   11964:	e59d901c 	ldr	r9, [sp, #28]
   11968:	e092200a 	adds	r2, r2, sl
   1196c:	e59da020 	ldr	sl, [sp, #32]
   11970:	e0a3300b 	adc	r3, r3, fp
   11974:	e59db024 	ldr	fp, [sp, #36]	; 0x24
   11978:	e0900008 	adds	r0, r0, r8
   1197c:	e59d8000 	ldr	r8, [sp]
   11980:	e0a11009 	adc	r1, r1, r9
   11984:	e59d9004 	ldr	r9, [sp, #4]
   11988:	e092200a 	adds	r2, r2, sl
   1198c:	e59da008 	ldr	sl, [sp, #8]
   11990:	e0a3300b 	adc	r3, r3, fp
   11994:	e59db00c 	ldr	fp, [sp, #12]
   11998:	e0944008 	adds	r4, r4, r8
   1199c:	e0a55009 	adc	r5, r5, r9
   119a0:	e096600a 	adds	r6, r6, sl
   119a4:	e0a7700b 	adc	r7, r7, fp
   119a8:	e59da030 	ldr	sl, [sp, #48]	; 0x30
   119ac:	e59db034 	ldr	fp, [sp, #52]	; 0x34
   119b0:	e2966003 	adds	r6, r6, #3
   119b4:	e2a77000 	adc	r7, r7, #0
   119b8:	e094400a 	adds	r4, r4, sl
   119bc:	e0a5500b 	adc	r5, r5, fp
   119c0:	e0900002 	adds	r0, r0, r2
   119c4:	e0a11003 	adc	r1, r1, r3
   119c8:	e0944006 	adds	r4, r4, r6
   119cc:	e02183a2 	eor	r8, r1, r2, lsr #7
   119d0:	e0a55007 	adc	r5, r5, r7
   119d4:	e0202c82 	eor	r2, r0, r2, lsl #25
   119d8:	e0259086 	eor	r9, r5, r6, lsl #1
   119dc:	e02223a3 	eor	r2, r2, r3, lsr #7
   119e0:	e0246fa6 	eor	r6, r4, r6, lsr #31
   119e4:	e0283c83 	eor	r3, r8, r3, lsl #25
   119e8:	e0266087 	eor	r6, r6, r7, lsl #1
   119ec:	e0297fa7 	eor	r7, r9, r7, lsr #31
   119f0:	e0944002 	adds	r4, r4, r2
   119f4:	e0a55003 	adc	r5, r5, r3
   119f8:	e0900006 	adds	r0, r0, r6
   119fc:	e0258a22 	eor	r8, r5, r2, lsr #20
   11a00:	e0a11007 	adc	r1, r1, r7
   11a04:	e0242602 	eor	r2, r4, r2, lsl #12
   11a08:	e0219706 	eor	r9, r1, r6, lsl #14
   11a0c:	e0222a23 	eor	r2, r2, r3, lsr #20
   11a10:	e0206926 	eor	r6, r0, r6, lsr #18
   11a14:	e0283603 	eor	r3, r8, r3, lsl #12
   11a18:	e0266707 	eor	r6, r6, r7, lsl #14
   11a1c:	e0297927 	eor	r7, r9, r7, lsr #18
   11a20:	e0900002 	adds	r0, r0, r2
   11a24:	e0a11003 	adc	r1, r1, r3
   11a28:	e0944006 	adds	r4, r4, r6
   11a2c:	e0218d02 	eor	r8, r1, r2, lsl #26
   11a30:	e0a55007 	adc	r5, r5, r7
   11a34:	e0202322 	eor	r2, r0, r2, lsr #6
   11a38:	e0259526 	eor	r9, r5, r6, lsr #10
   11a3c:	e0222d03 	eor	r2, r2, r3, lsl #26
   11a40:	e0246b06 	eor	r6, r4, r6, lsl #22
   11a44:	e0283323 	eor	r3, r8, r3, lsr #6
   11a48:	e0266527 	eor	r6, r6, r7, lsr #10
   11a4c:	e0297b07 	eor	r7, r9, r7, lsl #22
   11a50:	e0944002 	adds	r4, r4, r2
   11a54:	e0a55003 	adc	r5, r5, r3
   11a58:	e0900006 	adds	r0, r0, r6
   11a5c:	e0248003 	eor	r8, r4, r3
   11a60:	e0a11007 	adc	r1, r1, r7
   11a64:	e0223005 	eor	r3, r2, r5
   11a68:	e0209007 	eor	r9, r0, r7
   11a6c:	e1a02008 	mov	r2, r8
   11a70:	e0267001 	eor	r7, r6, r1
   11a74:	e1a06009 	mov	r6, r9
   11a78:	e59d8020 	ldr	r8, [sp, #32]
   11a7c:	e59d9024 	ldr	r9, [sp, #36]	; 0x24
   11a80:	e092200a 	adds	r2, r2, sl
   11a84:	e59da000 	ldr	sl, [sp]
   11a88:	e0a3300b 	adc	r3, r3, fp
   11a8c:	e59db004 	ldr	fp, [sp, #4]
   11a90:	e0900008 	adds	r0, r0, r8
   11a94:	e59d8008 	ldr	r8, [sp, #8]
   11a98:	e0a11009 	adc	r1, r1, r9
   11a9c:	e59d900c 	ldr	r9, [sp, #12]
   11aa0:	e092200a 	adds	r2, r2, sl
   11aa4:	e59da010 	ldr	sl, [sp, #16]
   11aa8:	e0a3300b 	adc	r3, r3, fp
   11aac:	e59db014 	ldr	fp, [sp, #20]
   11ab0:	e0944008 	adds	r4, r4, r8
   11ab4:	e0a55009 	adc	r5, r5, r9
   11ab8:	e096600a 	adds	r6, r6, sl
   11abc:	e0a7700b 	adc	r7, r7, fp
   11ac0:	e59da038 	ldr	sl, [sp, #56]	; 0x38
   11ac4:	e59db03c 	ldr	fp, [sp, #60]	; 0x3c
   11ac8:	e2966004 	adds	r6, r6, #4
   11acc:	e2a77000 	adc	r7, r7, #0
   11ad0:	e094400a 	adds	r4, r4, sl
   11ad4:	e0a5500b 	adc	r5, r5, fp
   11ad8:	e0900002 	adds	r0, r0, r2
   11adc:	e0a11003 	adc	r1, r1, r3
   11ae0:	e0944006 	adds	r4, r4, r6
   11ae4:	e0218922 	eor	r8, r1, r2, lsr #18
   11ae8:	e0a55007 	adc	r5, r5, r7
   11aec:	e0202702 	eor	r2, r0, r2, lsl #14
   11af0:	e0259826 	eor	r9, r5, r6, lsr #16
   11af4:	e0222923 	eor	r2, r2, r3, lsr #18
   11af8:	e0246806 	eor	r6, r4, r6, lsl #16
   11afc:	e0283703 	eor	r3, r8, r3, lsl #14
   11b00:	e0266827 	eor	r6, r6, r7, lsr #16
   11b04:	e0297807 	eor	r7, r9, r7, lsl #16
   11b08:	e0944002 	adds	r4, r4, r2
   11b0c:	e0a55003 	adc	r5, r5, r3
   11b10:	e0900006 	adds	r0, r0, r6
   11b14:	e0258c82 	eor	r8, r5, r2, lsl #25
   11b18:	e0a11007 	adc	r1, r1, r7
   11b1c:	e02423a2 	eor	r2, r4, r2, lsr #7
   11b20:	e0219a06 	eor	r9, r1, r6, lsl #20
   11b24:	e0222c83 	eor	r2, r2, r3, lsl #25
   11b28:	e0206626 	eor	r6, r0, r6, lsr #12
   11b2c:	e02833a3 	eor	r3, r8, r3, lsr #7
   11b30:	e0266a07 	eor	r6, r6, r7, lsl #20
   11b34:	e0297627 	eor	r7, r9, r7, lsr #12
   11b38:	e0900002 	adds	r0, r0, r2
   11b3c:	e0a11003 	adc	r1, r1, r3
   11b40:	e0944006 	adds	r4, r4, r6
   11b44:	e02184a2 	eor	r8, r1, r2, lsr #9
   11b48:	e0a55007 	adc	r5, r5, r7
   11b4c:	e0202b82 	eor	r2, r0, r2, lsl #23
   11b50:	e0259406 	eor	r9, r5, r6, lsl #8
   11b54:	e02224a3 	eor	r2, r2, r3, lsr #9
   11b58:	e0246c26 	eor	r6, r4, r6, lsr #24
   11b5c:	e0283b83 	eor	r3, r8, r3, lsl #23
   11b60:	e0266407 	eor	r6, r6, r7, lsl #8
   11b64:	e0297c27 	eor	r7, r9, r7, lsr #24
   11b68:	e0944002 	adds	r4, r4, r2
   11b6c:	e0a55003 	adc	r5, r5, r3
   11b70:	e0900006 	adds	r0, r0, r6
   11b74:	e0258282 	eor	r8, r5, r2, lsl #5
   11b78:	e0a11007 	adc	r1, r1, r7
   11b7c:	e0242da2 	eor	r2, r4, r2, lsr #27
   11b80:	e0219da6 	eor	r9, r1, r6, lsr #27
   11b84:	e0222283 	eor	r2, r2, r3, lsl #5
   11b88:	e0206286 	eor	r6, r0, r6, lsl #5
   11b8c:	e0283da3 	eor	r3, r8, r3, lsr #27
   11b90:	e0266da7 	eor	r6, r6, r7, lsr #27
   11b94:	e0297287 	eor	r7, r9, r7, lsl #5
   11b98:	e59d8000 	ldr	r8, [sp]
   11b9c:	e59d9004 	ldr	r9, [sp, #4]
   11ba0:	e092200a 	adds	r2, r2, sl
   11ba4:	e59da008 	ldr	sl, [sp, #8]
   11ba8:	e0a3300b 	adc	r3, r3, fp
   11bac:	e59db00c 	ldr	fp, [sp, #12]
   11bb0:	e0900008 	adds	r0, r0, r8
   11bb4:	e59d8010 	ldr	r8, [sp, #16]
   11bb8:	e0a11009 	adc	r1, r1, r9
   11bbc:	e59d9014 	ldr	r9, [sp, #20]
   11bc0:	e092200a 	adds	r2, r2, sl
   11bc4:	e59da018 	ldr	sl, [sp, #24]
   11bc8:	e0a3300b 	adc	r3, r3, fp
   11bcc:	e59db01c 	ldr	fp, [sp, #28]
   11bd0:	e0944008 	adds	r4, r4, r8
   11bd4:	e0a55009 	adc	r5, r5, r9
   11bd8:	e096600a 	adds	r6, r6, sl
   11bdc:	e0a7700b 	adc	r7, r7, fp
   11be0:	e59da028 	ldr	sl, [sp, #40]	; 0x28
   11be4:	e59db02c 	ldr	fp, [sp, #44]	; 0x2c
   11be8:	e2966005 	adds	r6, r6, #5
   11bec:	e2a77000 	adc	r7, r7, #0
   11bf0:	e094400a 	adds	r4, r4, sl
   11bf4:	e0a5500b 	adc	r5, r5, fp
   11bf8:	e0900002 	adds	r0, r0, r2
   11bfc:	e0a11003 	adc	r1, r1, r3
   11c00:	e0944006 	adds	r4, r4, r6
   11c04:	e02183a2 	eor	r8, r1, r2, lsr #7
   11c08:	e0a55007 	adc	r5, r5, r7
   11c0c:	e0202c82 	eor	r2, r0, r2, lsl #25
   11c10:	e0259086 	eor	r9, r5, r6, lsl #1
   11c14:	e02223a3 	eor	r2, r2, r3, lsr #7
   11c18:	e0246fa6 	eor	r6, r4, r6, lsr #31
   11c1c:	e0283c83 	eor	r3, r8, r3, lsl #25
   11c20:	e0266087 	eor	r6, r6, r7, lsl #1
   11c24:	e0297fa7 	eor	r7, r9, r7, lsr #31
   11c28:	e0944002 	adds	r4, r4, r2
   11c2c:	e0a55003 	adc	r5, r5, r3
   11c30:	e0900006 	adds	r0, r0, r6
   11c34:	e0258a22 	eor	r8, r5, r2, lsr #20
   11c38:	e0a11007 	adc	r1, r1, r7
   11c3c:	e0242602 	eor	r2, r4, r2, lsl #12
   11c40:	e0219706 	eor	r9, r1, r6, lsl #14
   11c44:	e0222a23 	eor	r2, r2, r3, lsr #20
   11c48:	e0206926 	eor	r6, r0, r6, lsr #18
   11c4c:	e0283603 	eor	r3, r8, r3, lsl #12
   11c50:	e0266707 	eor	r6, r6, r7, lsl #14
   11c54:	e0297927 	eor	r7, r9, r7, lsr #18
   11c58:	e0900002 	adds	r0, r0, r2
   11c5c:	e0a11003 	adc	r1, r1, r3
   11c60:	e0944006 	adds	r4, r4, r6
   11c64:	e0218d02 	eor	r8, r1, r2, lsl #26
   11c68:	e0a55007 	adc	r5, r5, r7
   11c6c:	e0202322 	eor	r2, r0, r2, lsr #6
   11c70:	e0259526 	eor	r9, r5, r6, lsr #10
   11c74:	e0222d03 	eor	r2, r2, r3, lsl #26
   11c78:	e0246b06 	eor	r6, r4, r6, lsl #22
   11c7c:	e0283323 	eor	r3, r8, r3, lsr #6
   11c80:	e0266527 	eor	r6, r6, r7, lsr #10
   11c84:	e0297b07 	eor	r7, r9, r7, lsl #22
   11c88:	e0944002 	adds	r4, r4, r2
   11c8c:	e0a55003 	adc	r5, r5, r3
   11c90:	e0900006 	adds	r0, r0, r6
   11c94:	e0248003 	eor	r8, r4, r3
   11c98:	e0a11007 	adc	r1, r1, r7
   11c9c:	e0223005 	eor	r3, r2, r5
   11ca0:	e0209007 	eor	r9, r0, r7
   11ca4:	e1a02008 	mov	r2, r8
   11ca8:	e0267001 	eor	r7, r6, r1
   11cac:	e1a06009 	mov	r6, r9
   11cb0:	e59d8008 	ldr	r8, [sp, #8]
   11cb4:	e59d900c 	ldr	r9, [sp, #12]
   11cb8:	e092200a 	adds	r2, r2, sl
   11cbc:	e59da010 	ldr	sl, [sp, #16]
   11cc0:	e0a3300b 	adc	r3, r3, fp
   11cc4:	e59db014 	ldr	fp, [sp, #20]
   11cc8:	e0900008 	adds	r0, r0, r8
   11ccc:	e59d8018 	ldr	r8, [sp, #24]
   11cd0:	e0a11009 	adc	r1, r1, r9
   11cd4:	e59d901c 	ldr	r9, [sp, #28]
   11cd8:	e092200a 	adds	r2, r2, sl
   11cdc:	e59da020 	ldr	sl, [sp, #32]
   11ce0:	e0a3300b 	adc	r3, r3, fp
   11ce4:	e59db024 	ldr	fp, [sp, #36]	; 0x24
   11ce8:	e0944008 	adds	r4, r4, r8
   11cec:	e0a55009 	adc	r5, r5, r9
   11cf0:	e096600a 	adds	r6, r6, sl
   11cf4:	e0a7700b 	adc	r7, r7, fp
   11cf8:	e59da030 	ldr	sl, [sp, #48]	; 0x30
   11cfc:	e59db034 	ldr	fp, [sp, #52]	; 0x34
   11d00:	e2966006 	adds	r6, r6, #6
   11d04:	e2a77000 	adc	r7, r7, #0
   11d08:	e094400a 	adds	r4, r4, sl
   11d0c:	e0a5500b 	adc	r5, r5, fp
   11d10:	e0900002 	adds	r0, r0, r2
   11d14:	e0a11003 	adc	r1, r1, r3
   11d18:	e0944006 	adds	r4, r4, r6
   11d1c:	e0218922 	eor	r8, r1, r2, lsr #18
   11d20:	e0a55007 	adc	r5, r5, r7
   11d24:	e0202702 	eor	r2, r0, r2, lsl #14
   11d28:	e0259826 	eor	r9, r5, r6, lsr #16
   11d2c:	e0222923 	eor	r2, r2, r3, lsr #18
   11d30:	e0246806 	eor	r6, r4, r6, lsl #16
   11d34:	e0283703 	eor	r3, r8, r3, lsl #14
   11d38:	e0266827 	eor	r6, r6, r7, lsr #16
   11d3c:	e0297807 	eor	r7, r9, r7, lsl #16
   11d40:	e0944002 	adds	r4, r4, r2
   11d44:	e0a55003 	adc	r5, r5, r3
   11d48:	e0900006 	adds	r0, r0, r6
   11d4c:	e0258c82 	eor	r8, r5, r2, lsl #25
   11d50:	e0a11007 	adc	r1, r1, r7
   11d54:	e02423a2 	eor	r2, r4, r2, lsr #7
   11d58:	e0219a06 	eor	r9, r1, r6, lsl #20
   11d5c:	e0222c83 	eor	r2, r2, r3, lsl #25
   11d60:	e0206626 	eor	r6, r0, r6, lsr #12
   11d64:	e02833a3 	eor	r3, r8, r3, lsr #7
   11d68:	e0266a07 	eor	r6, r6, r7, lsl #20
   11d6c:	e0297627 	eor	r7, r9, r7, lsr #12
   11d70:	e0900002 	adds	r0, r0, r2
   11d74:	e0a11003 	adc	r1, r1, r3
   11d78:	e0944006 	adds	r4, r4, r6
   11d7c:	e02184a2 	eor	r8, r1, r2, lsr #9
   11d80:	e0a55007 	adc	r5, r5, r7
   11d84:	e0202b82 	eor	r2, r0, r2, lsl #23
   11d88:	e0259406 	eor	r9, r5, r6, lsl #8
   11d8c:	e02224a3 	eor	r2, r2, r3, lsr #9
   11d90:	e0246c26 	eor	r6, r4, r6, lsr #24
   11d94:	e0283b83 	eor	r3, r8, r3, lsl #23
   11d98:	e0266407 	eor	r6, r6, r7, lsl #8
   11d9c:	e0297c27 	eor	r7, r9, r7, lsr #24
   11da0:	e0944002 	adds	r4, r4, r2
   11da4:	e0a55003 	adc	r5, r5, r3
   11da8:	e0900006 	adds	r0, r0, r6
   11dac:	e0258282 	eor	r8, r5, r2, lsl #5
   11db0:	e0a11007 	adc	r1, r1, r7
   11db4:	e0242da2 	eor	r2, r4, r2, lsr #27
   11db8:	e0219da6 	eor	r9, r1, r6, lsr #27
   11dbc:	e0222283 	eor	r2, r2, r3, lsl #5
   11dc0:	e0206286 	eor	r6, r0, r6, lsl #5
   11dc4:	e0283da3 	eor	r3, r8, r3, lsr #27
   11dc8:	e0266da7 	eor	r6, r6, r7, lsr #27
   11dcc:	e0297287 	eor	r7, r9, r7, lsl #5
   11dd0:	e59d8010 	ldr	r8, [sp, #16]
   11dd4:	e59d9014 	ldr	r9, [sp, #20]
   11dd8:	e092200a 	adds	r2, r2, sl
   11ddc:	e59da018 	ldr	sl, [sp, #24]
   11de0:	e0a3300b 	adc	r3, r3, fp
   11de4:	e59db01c 	ldr	fp, [sp, #28]
   11de8:	e0900008 	adds	r0, r0, r8
   11dec:	e59d8020 	ldr	r8, [sp, #32]
   11df0:	e0a11009 	adc	r1, r1, r9
   11df4:	e59d9024 	ldr	r9, [sp, #36]	; 0x24
   11df8:	e092200a 	adds	r2, r2, sl
   11dfc:	e59da000 	ldr	sl, [sp]
   11e00:	e0a3300b 	adc	r3, r3, fp
   11e04:	e59db004 	ldr	fp, [sp, #4]
   11e08:	e0944008 	adds	r4, r4, r8
   11e0c:	e0a55009 	adc	r5, r5, r9
   11e10:	e096600a 	adds	r6, r6, sl
   11e14:	e0a7700b 	adc	r7, r7, fp
   11e18:	e59da038 	ldr	sl, [sp, #56]	; 0x38
   11e1c:	e59db03c 	ldr	fp, [sp, #60]	; 0x3c
   11e20:	e2966007 	adds	r6, r6, #7
   11e24:	e2a77000 	adc	r7, r7, #0
   11e28:	e094400a 	adds	r4, r4, sl
   11e2c:	e0a5500b 	adc	r5, r5, fp
   11e30:	e0900002 	adds	r0, r0, r2
   11e34:	e0a11003 	adc	r1, r1, r3
   11e38:	e0944006 	adds	r4, r4, r6
   11e3c:	e02183a2 	eor	r8, r1, r2, lsr #7
   11e40:	e0a55007 	adc	r5, r5, r7
   11e44:	e0202c82 	eor	r2, r0, r2, lsl #25
   11e48:	e0259086 	eor	r9, r5, r6, lsl #1
   11e4c:	e02223a3 	eor	r2, r2, r3, lsr #7
   11e50:	e0246fa6 	eor	r6, r4, r6, lsr #31
   11e54:	e0283c83 	eor	r3, r8, r3, lsl #25
   11e58:	e0266087 	eor	r6, r6, r7, lsl #1
   11e5c:	e0297fa7 	eor	r7, r9, r7, lsr #31
   11e60:	e0944002 	adds	r4, r4, r2
   11e64:	e0a55003 	adc	r5, r5, r3
   11e68:	e0900006 	adds	r0, r0, r6
   11e6c:	e0258a22 	eor	r8, r5, r2, lsr #20
   11e70:	e0a11007 	adc	r1, r1, r7
   11e74:	e0242602 	eor	r2, r4, r2, lsl #12
   11e78:	e0219706 	eor	r9, r1, r6, lsl #14
   11e7c:	e0222a23 	eor	r2, r2, r3, lsr #20
   11e80:	e0206926 	eor	r6, r0, r6, lsr #18
   11e84:	e0283603 	eor	r3, r8, r3, lsl #12
   11e88:	e0266707 	eor	r6, r6, r7, lsl #14
   11e8c:	e0297927 	eor	r7, r9, r7, lsr #18
   11e90:	e0900002 	adds	r0, r0, r2
   11e94:	e0a11003 	adc	r1, r1, r3
   11e98:	e0944006 	adds	r4, r4, r6
   11e9c:	e0218d02 	eor	r8, r1, r2, lsl #26
   11ea0:	e0a55007 	adc	r5, r5, r7
   11ea4:	e0202322 	eor	r2, r0, r2, lsr #6
   11ea8:	e0259526 	eor	r9, r5, r6, lsr #10
   11eac:	e0222d03 	eor	r2, r2, r3, lsl #26
   11eb0:	e0246b06 	eor	r6, r4, r6, lsl #22
   11eb4:	e0283323 	eor	r3, r8, r3, lsr #6
   11eb8:	e0266527 	eor	r6, r6, r7, lsr #10
   11ebc:	e0297b07 	eor	r7, r9, r7, lsl #22
   11ec0:	e0944002 	adds	r4, r4, r2
   11ec4:	e0a55003 	adc	r5, r5, r3
   11ec8:	e0900006 	adds	r0, r0, r6
   11ecc:	e0248003 	eor	r8, r4, r3
   11ed0:	e0a11007 	adc	r1, r1, r7
   11ed4:	e0223005 	eor	r3, r2, r5
   11ed8:	e0209007 	eor	r9, r0, r7
   11edc:	e1a02008 	mov	r2, r8
   11ee0:	e0267001 	eor	r7, r6, r1
   11ee4:	e1a06009 	mov	r6, r9
   11ee8:	e59d8018 	ldr	r8, [sp, #24]
   11eec:	e59d901c 	ldr	r9, [sp, #28]
   11ef0:	e092200a 	adds	r2, r2, sl
   11ef4:	e59da020 	ldr	sl, [sp, #32]
   11ef8:	e0a3300b 	adc	r3, r3, fp
   11efc:	e59db024 	ldr	fp, [sp, #36]	; 0x24
   11f00:	e0900008 	adds	r0, r0, r8
   11f04:	e59d8000 	ldr	r8, [sp]
   11f08:	e0a11009 	adc	r1, r1, r9
   11f0c:	e59d9004 	ldr	r9, [sp, #4]
   11f10:	e092200a 	adds	r2, r2, sl
   11f14:	e59da008 	ldr	sl, [sp, #8]
   11f18:	e0a3300b 	adc	r3, r3, fp
   11f1c:	e59db00c 	ldr	fp, [sp, #12]
   11f20:	e0944008 	adds	r4, r4, r8
   11f24:	e0a55009 	adc	r5, r5, r9
   11f28:	e096600a 	adds	r6, r6, sl
   11f2c:	e0a7700b 	adc	r7, r7, fp
   11f30:	e59da028 	ldr	sl, [sp, #40]	; 0x28
   11f34:	e59db02c 	ldr	fp, [sp, #44]	; 0x2c
   11f38:	e2966008 	adds	r6, r6, #8
   11f3c:	e2a77000 	adc	r7, r7, #0
   11f40:	e094400a 	adds	r4, r4, sl
   11f44:	e0a5500b 	adc	r5, r5, fp
   11f48:	e0900002 	adds	r0, r0, r2
   11f4c:	e0a11003 	adc	r1, r1, r3
   11f50:	e0944006 	adds	r4, r4, r6
   11f54:	e0218922 	eor	r8, r1, r2, lsr #18
   11f58:	e0a55007 	adc	r5, r5, r7
   11f5c:	e0202702 	eor	r2, r0, r2, lsl #14
   11f60:	e0259826 	eor	r9, r5, r6, lsr #16
   11f64:	e0222923 	eor	r2, r2, r3, lsr #18
   11f68:	e0246806 	eor	r6, r4, r6, lsl #16
   11f6c:	e0283703 	eor	r3, r8, r3, lsl #14
   11f70:	e0266827 	eor	r6, r6, r7, lsr #16
   11f74:	e0297807 	eor	r7, r9, r7, lsl #16
   11f78:	e0944002 	adds	r4, r4, r2
   11f7c:	e0a55003 	adc	r5, r5, r3
   11f80:	e0900006 	adds	r0, r0, r6
   11f84:	e0258c82 	eor	r8, r5, r2, lsl #25
   11f88:	e0a11007 	adc	r1, r1, r7
   11f8c:	e02423a2 	eor	r2, r4, r2, lsr #7
   11f90:	e0219a06 	eor	r9, r1, r6, lsl #20
   11f94:	e0222c83 	eor	r2, r2, r3, lsl #25
   11f98:	e0206626 	eor	r6, r0, r6, lsr #12
   11f9c:	e02833a3 	eor	r3, r8, r3, lsr #7
   11fa0:	e0266a07 	eor	r6, r6, r7, lsl #20
   11fa4:	e0297627 	eor	r7, r9, r7, lsr #12
   11fa8:	e0900002 	adds	r0, r0, r2
   11fac:	e0a11003 	adc	r1, r1, r3
   11fb0:	e0944006 	adds	r4, r4, r6
   11fb4:	e02184a2 	eor	r8, r1, r2, lsr #9
   11fb8:	e0a55007 	adc	r5, r5, r7
   11fbc:	e0202b82 	eor	r2, r0, r2, lsl #23
   11fc0:	e0259406 	eor	r9, r5, r6, lsl #8
   11fc4:	e02224a3 	eor	r2, r2, r3, lsr #9
   11fc8:	e0246c26 	eor	r6, r4, r6, lsr #24
   11fcc:	e0283b83 	eor	r3, r8, r3, lsl #23
   11fd0:	e0266407 	eor	r6, r6, r7, lsl #8
   11fd4:	e0297c27 	eor	r7, r9, r7, lsr #24
   11fd8:	e0944002 	adds	r4, r4, r2
   11fdc:	e0a55003 	adc	r5, r5, r3
   11fe0:	e0900006 	adds	r0, r0, r6
   11fe4:	e0258282 	eor	r8, r5, r2, lsl #5
   11fe8:	e0a11007 	adc	r1, r1, r7
   11fec:	e0242da2 	eor	r2, r4, r2, lsr #27
   11ff0:	e0219da6 	eor	r9, r1, r6, lsr #27
   11ff4:	e0222283 	eor	r2, r2, r3, lsl #5
   11ff8:	e0206286 	eor	r6, r0, r6, lsl #5
   11ffc:	e0283da3 	eor	r3, r8, r3, lsr #27
   12000:	e0266da7 	eor	r6, r6, r7, lsr #27
   12004:	e0297287 	eor	r7, r9, r7, lsl #5
   12008:	e59d8020 	ldr	r8, [sp, #32]
   1200c:	e59d9024 	ldr	r9, [sp, #36]	; 0x24
   12010:	e092200a 	adds	r2, r2, sl
   12014:	e59da000 	ldr	sl, [sp]
   12018:	e0a3300b 	adc	r3, r3, fp
   1201c:	e59db004 	ldr	fp, [sp, #4]
   12020:	e0900008 	adds	r0, r0, r8
   12024:	e59d8008 	ldr	r8, [sp, #8]
   12028:	e0a11009 	adc	r1, r1, r9
   1202c:	e59d900c 	ldr	r9, [sp, #12]
   12030:	e092200a 	adds	r2, r2, sl
   12034:	e59da010 	ldr	sl, [sp, #16]
   12038:	e0a3300b 	adc	r3, r3, fp
   1203c:	e59db014 	ldr	fp, [sp, #20]
   12040:	e0944008 	adds	r4, r4, r8
   12044:	e0a55009 	adc	r5, r5, r9
   12048:	e096600a 	adds	r6, r6, sl
   1204c:	e0a7700b 	adc	r7, r7, fp
   12050:	e59da030 	ldr	sl, [sp, #48]	; 0x30
   12054:	e59db034 	ldr	fp, [sp, #52]	; 0x34
   12058:	e2966009 	adds	r6, r6, #9
   1205c:	e2a77000 	adc	r7, r7, #0
   12060:	e094400a 	adds	r4, r4, sl
   12064:	e0a5500b 	adc	r5, r5, fp
   12068:	e0900002 	adds	r0, r0, r2
   1206c:	e0a11003 	adc	r1, r1, r3
   12070:	e0944006 	adds	r4, r4, r6
   12074:	e02183a2 	eor	r8, r1, r2, lsr #7
   12078:	e0a55007 	adc	r5, r5, r7
   1207c:	e0202c82 	eor	r2, r0, r2, lsl #25
   12080:	e0259086 	eor	r9, r5, r6, lsl #1
   12084:	e02223a3 	eor	r2, r2, r3, lsr #7
   12088:	e0246fa6 	eor	r6, r4, r6, lsr #31
   1208c:	e0283c83 	eor	r3, r8, r3, lsl #25
   12090:	e0266087 	eor	r6, r6, r7, lsl #1
   12094:	e0297fa7 	eor	r7, r9, r7, lsr #31
   12098:	e0944002 	adds	r4, r4, r2
   1209c:	e0a55003 	adc	r5, r5, r3
   120a0:	e0900006 	adds	r0, r0, r6
   120a4:	e0258a22 	eor	r8, r5, r2, lsr #20
   120a8:	e0a11007 	adc	r1, r1, r7
   120ac:	e0242602 	eor	r2, r4, r2, lsl #12
   120b0:	e0219706 	eor	r9, r1, r6, lsl #14
   120b4:	e0222a23 	eor	r2, r2, r3, lsr #20
   120b8:	e0206926 	eor	r6, r0, r6, lsr #18
   120bc:	e0283603 	eor	r3, r8, r3, lsl #12
   120c0:	e0266707 	eor	r6, r6, r7, lsl #14
   120c4:	e0297927 	eor	r7, r9, r7, lsr #18
   120c8:	e0900002 	adds	r0, r0, r2
   120cc:	e0a11003 	adc	r1, r1, r3
   120d0:	e0944006 	adds	r4, r4, r6
   120d4:	e0218d02 	eor	r8, r1, r2, lsl #26
   120d8:	e0a55007 	adc	r5, r5, r7
   120dc:	e0202322 	eor	r2, r0, r2, lsr #6
   120e0:	e0259526 	eor	r9, r5, r6, lsr #10
   120e4:	e0222d03 	eor	r2, r2, r3, lsl #26
   120e8:	e0246b06 	eor	r6, r4, r6, lsl #22
   120ec:	e0283323 	eor	r3, r8, r3, lsr #6
   120f0:	e0266527 	eor	r6, r6, r7, lsr #10
   120f4:	e0297b07 	eor	r7, r9, r7, lsl #22
   120f8:	e0944002 	adds	r4, r4, r2
   120fc:	e0a55003 	adc	r5, r5, r3
   12100:	e0900006 	adds	r0, r0, r6
   12104:	e0248003 	eor	r8, r4, r3
   12108:	e0a11007 	adc	r1, r1, r7
   1210c:	e0223005 	eor	r3, r2, r5
   12110:	e0209007 	eor	r9, r0, r7
   12114:	e1a02008 	mov	r2, r8
   12118:	e0267001 	eor	r7, r6, r1
   1211c:	e1a06009 	mov	r6, r9
   12120:	e59d8000 	ldr	r8, [sp]
   12124:	e59d9004 	ldr	r9, [sp, #4]
   12128:	e092200a 	adds	r2, r2, sl
   1212c:	e59da008 	ldr	sl, [sp, #8]
   12130:	e0a3300b 	adc	r3, r3, fp
   12134:	e59db00c 	ldr	fp, [sp, #12]
   12138:	e0900008 	adds	r0, r0, r8
   1213c:	e59d8010 	ldr	r8, [sp, #16]
   12140:	e0a11009 	adc	r1, r1, r9
   12144:	e59d9014 	ldr	r9, [sp, #20]
   12148:	e092200a 	adds	r2, r2, sl
   1214c:	e59da018 	ldr	sl, [sp, #24]
   12150:	e0a3300b 	adc	r3, r3, fp
   12154:	e59db01c 	ldr	fp, [sp, #28]
   12158:	e0944008 	adds	r4, r4, r8
   1215c:	e0a55009 	adc	r5, r5, r9
   12160:	e096600a 	adds	r6, r6, sl
   12164:	e0a7700b 	adc	r7, r7, fp
   12168:	e59da038 	ldr	sl, [sp, #56]	; 0x38
   1216c:	e59db03c 	ldr	fp, [sp, #60]	; 0x3c
   12170:	e296600a 	adds	r6, r6, #10
   12174:	e2a77000 	adc	r7, r7, #0
   12178:	e094400a 	adds	r4, r4, sl
   1217c:	e0a5500b 	adc	r5, r5, fp
   12180:	e0900002 	adds	r0, r0, r2
   12184:	e0a11003 	adc	r1, r1, r3
   12188:	e0944006 	adds	r4, r4, r6
   1218c:	e0218922 	eor	r8, r1, r2, lsr #18
   12190:	e0a55007 	adc	r5, r5, r7
   12194:	e0202702 	eor	r2, r0, r2, lsl #14
   12198:	e0259826 	eor	r9, r5, r6, lsr #16
   1219c:	e0222923 	eor	r2, r2, r3, lsr #18
   121a0:	e0246806 	eor	r6, r4, r6, lsl #16
   121a4:	e0283703 	eor	r3, r8, r3, lsl #14
   121a8:	e0266827 	eor	r6, r6, r7, lsr #16
   121ac:	e0297807 	eor	r7, r9, r7, lsl #16
   121b0:	e0944002 	adds	r4, r4, r2
   121b4:	e0a55003 	adc	r5, r5, r3
   121b8:	e0900006 	adds	r0, r0, r6
   121bc:	e0258c82 	eor	r8, r5, r2, lsl #25
   121c0:	e0a11007 	adc	r1, r1, r7
   121c4:	e02423a2 	eor	r2, r4, r2, lsr #7
   121c8:	e0219a06 	eor	r9, r1, r6, lsl #20
   121cc:	e0222c83 	eor	r2, r2, r3, lsl #25
   121d0:	e0206626 	eor	r6, r0, r6, lsr #12
   121d4:	e02833a3 	eor	r3, r8, r3, lsr #7
   121d8:	e0266a07 	eor	r6, r6, r7, lsl #20
   121dc:	e0297627 	eor	r7, r9, r7, lsr #12
   121e0:	e0900002 	adds	r0, r0, r2
   121e4:	e0a11003 	adc	r1, r1, r3
   121e8:	e0944006 	adds	r4, r4, r6
   121ec:	e02184a2 	eor	r8, r1, r2, lsr #9
   121f0:	e0a55007 	adc	r5, r5, r7
   121f4:	e0202b82 	eor	r2, r0, r2, lsl #23
   121f8:	e0259406 	eor	r9, r5, r6, lsl #8
   121fc:	e02224a3 	eor	r2, r2, r3, lsr #9
   12200:	e0246c26 	eor	r6, r4, r6, lsr #24
   12204:	e0283b83 	eor	r3, r8, r3, lsl #23
   12208:	e0266407 	eor	r6, r6, r7, lsl #8
   1220c:	e0297c27 	eor	r7, r9, r7, lsr #24
   12210:	e0944002 	adds	r4, r4, r2
   12214:	e0a55003 	adc	r5, r5, r3
   12218:	e0900006 	adds	r0, r0, r6
   1221c:	e0258282 	eor	r8, r5, r2, lsl #5
   12220:	e0a11007 	adc	r1, r1, r7
   12224:	e0242da2 	eor	r2, r4, r2, lsr #27
   12228:	e0219da6 	eor	r9, r1, r6, lsr #27
   1222c:	e0222283 	eor	r2, r2, r3, lsl #5
   12230:	e0206286 	eor	r6, r0, r6, lsl #5
   12234:	e0283da3 	eor	r3, r8, r3, lsr #27
   12238:	e0266da7 	eor	r6, r6, r7, lsr #27
   1223c:	e0297287 	eor	r7, r9, r7, lsl #5
   12240:	e59d8008 	ldr	r8, [sp, #8]
   12244:	e59d900c 	ldr	r9, [sp, #12]
   12248:	e092200a 	adds	r2, r2, sl
   1224c:	e59da010 	ldr	sl, [sp, #16]
   12250:	e0a3300b 	adc	r3, r3, fp
   12254:	e59db014 	ldr	fp, [sp, #20]
   12258:	e0900008 	adds	r0, r0, r8
   1225c:	e59d8018 	ldr	r8, [sp, #24]
   12260:	e0a11009 	adc	r1, r1, r9
   12264:	e59d901c 	ldr	r9, [sp, #28]
   12268:	e092200a 	adds	r2, r2, sl
   1226c:	e59da020 	ldr	sl, [sp, #32]
   12270:	e0a3300b 	adc	r3, r3, fp
   12274:	e59db024 	ldr	fp, [sp, #36]	; 0x24
   12278:	e0944008 	adds	r4, r4, r8
   1227c:	e0a55009 	adc	r5, r5, r9
   12280:	e096600a 	adds	r6, r6, sl
   12284:	e0a7700b 	adc	r7, r7, fp
   12288:	e59da028 	ldr	sl, [sp, #40]	; 0x28
   1228c:	e59db02c 	ldr	fp, [sp, #44]	; 0x2c
   12290:	e296600b 	adds	r6, r6, #11
   12294:	e2a77000 	adc	r7, r7, #0
   12298:	e094400a 	adds	r4, r4, sl
   1229c:	e0a5500b 	adc	r5, r5, fp
   122a0:	e0900002 	adds	r0, r0, r2
   122a4:	e0a11003 	adc	r1, r1, r3
   122a8:	e0944006 	adds	r4, r4, r6
   122ac:	e02183a2 	eor	r8, r1, r2, lsr #7
   122b0:	e0a55007 	adc	r5, r5, r7
   122b4:	e0202c82 	eor	r2, r0, r2, lsl #25
   122b8:	e0259086 	eor	r9, r5, r6, lsl #1
   122bc:	e02223a3 	eor	r2, r2, r3, lsr #7
   122c0:	e0246fa6 	eor	r6, r4, r6, lsr #31
   122c4:	e0283c83 	eor	r3, r8, r3, lsl #25
   122c8:	e0266087 	eor	r6, r6, r7, lsl #1
   122cc:	e0297fa7 	eor	r7, r9, r7, lsr #31
   122d0:	e0944002 	adds	r4, r4, r2
   122d4:	e0a55003 	adc	r5, r5, r3
   122d8:	e0900006 	adds	r0, r0, r6
   122dc:	e0258a22 	eor	r8, r5, r2, lsr #20
   122e0:	e0a11007 	adc	r1, r1, r7
   122e4:	e0242602 	eor	r2, r4, r2, lsl #12
   122e8:	e0219706 	eor	r9, r1, r6, lsl #14
   122ec:	e0222a23 	eor	r2, r2, r3, lsr #20
   122f0:	e0206926 	eor	r6, r0, r6, lsr #18
   122f4:	e0283603 	eor	r3, r8, r3, lsl #12
   122f8:	e0266707 	eor	r6, r6, r7, lsl #14
   122fc:	e0297927 	eor	r7, r9, r7, lsr #18
   12300:	e0900002 	adds	r0, r0, r2
   12304:	e0a11003 	adc	r1, r1, r3
   12308:	e0944006 	adds	r4, r4, r6
   1230c:	e0218d02 	eor	r8, r1, r2, lsl #26
   12310:	e0a55007 	adc	r5, r5, r7
   12314:	e0202322 	eor	r2, r0, r2, lsr #6
   12318:	e0259526 	eor	r9, r5, r6, lsr #10
   1231c:	e0222d03 	eor	r2, r2, r3, lsl #26
   12320:	e0246b06 	eor	r6, r4, r6, lsl #22
   12324:	e0283323 	eor	r3, r8, r3, lsr #6
   12328:	e0266527 	eor	r6, r6, r7, lsr #10
   1232c:	e0297b07 	eor	r7, r9, r7, lsl #22
   12330:	e0944002 	adds	r4, r4, r2
   12334:	e0a55003 	adc	r5, r5, r3
   12338:	e0900006 	adds	r0, r0, r6
   1233c:	e0248003 	eor	r8, r4, r3
   12340:	e0a11007 	adc	r1, r1, r7
   12344:	e0223005 	eor	r3, r2, r5
   12348:	e0209007 	eor	r9, r0, r7
   1234c:	e1a02008 	mov	r2, r8
   12350:	e0267001 	eor	r7, r6, r1
   12354:	e1a06009 	mov	r6, r9
   12358:	e59d8010 	ldr	r8, [sp, #16]
   1235c:	e59d9014 	ldr	r9, [sp, #20]
   12360:	e092200a 	adds	r2, r2, sl
   12364:	e59da018 	ldr	sl, [sp, #24]
   12368:	e0a3300b 	adc	r3, r3, fp
   1236c:	e59db01c 	ldr	fp, [sp, #28]
   12370:	e0900008 	adds	r0, r0, r8
   12374:	e59d8020 	ldr	r8, [sp, #32]
   12378:	e0a11009 	adc	r1, r1, r9
   1237c:	e59d9024 	ldr	r9, [sp, #36]	; 0x24
   12380:	e092200a 	adds	r2, r2, sl
   12384:	e59da000 	ldr	sl, [sp]
   12388:	e0a3300b 	adc	r3, r3, fp
   1238c:	e59db004 	ldr	fp, [sp, #4]
   12390:	e0944008 	adds	r4, r4, r8
   12394:	e0a55009 	adc	r5, r5, r9
   12398:	e096600a 	adds	r6, r6, sl
   1239c:	e0a7700b 	adc	r7, r7, fp
   123a0:	e59da030 	ldr	sl, [sp, #48]	; 0x30
   123a4:	e59db034 	ldr	fp, [sp, #52]	; 0x34
   123a8:	e296600c 	adds	r6, r6, #12
   123ac:	e2a77000 	adc	r7, r7, #0
   123b0:	e094400a 	adds	r4, r4, sl
   123b4:	e0a5500b 	adc	r5, r5, fp
   123b8:	e0900002 	adds	r0, r0, r2
   123bc:	e0a11003 	adc	r1, r1, r3
   123c0:	e0944006 	adds	r4, r4, r6
   123c4:	e0218922 	eor	r8, r1, r2, lsr #18
   123c8:	e0a55007 	adc	r5, r5, r7
   123cc:	e0202702 	eor	r2, r0, r2, lsl #14
   123d0:	e0259826 	eor	r9, r5, r6, lsr #16
   123d4:	e0222923 	eor	r2, r2, r3, lsr #18
   123d8:	e0246806 	eor	r6, r4, r6, lsl #16
   123dc:	e0283703 	eor	r3, r8, r3, lsl #14
   123e0:	e0266827 	eor	r6, r6, r7, lsr #16
   123e4:	e0297807 	eor	r7, r9, r7, lsl #16
   123e8:	e0944002 	adds	r4, r4, r2
   123ec:	e0a55003 	adc	r5, r5, r3
   123f0:	e0900006 	adds	r0, r0, r6
   123f4:	e0258c82 	eor	r8, r5, r2, lsl #25
   123f8:	e0a11007 	adc	r1, r1, r7
   123fc:	e02423a2 	eor	r2, r4, r2, lsr #7
   12400:	e0219a06 	eor	r9, r1, r6, lsl #20
   12404:	e0222c83 	eor	r2, r2, r3, lsl #25
   12408:	e0206626 	eor	r6, r0, r6, lsr #12
   1240c:	e02833a3 	eor	r3, r8, r3, lsr #7
   12410:	e0266a07 	eor	r6, r6, r7, lsl #20
   12414:	e0297627 	eor	r7, r9, r7, lsr #12
   12418:	e0900002 	adds	r0, r0, r2
   1241c:	e0a11003 	adc	r1, r1, r3
   12420:	e0944006 	adds	r4, r4, r6
   12424:	e02184a2 	eor	r8, r1, r2, lsr #9
   12428:	e0a55007 	adc	r5, r5, r7
   1242c:	e0202b82 	eor	r2, r0, r2, lsl #23
   12430:	e0259406 	eor	r9, r5, r6, lsl #8
   12434:	e02224a3 	eor	r2, r2, r3, lsr #9
   12438:	e0246c26 	eor	r6, r4, r6, lsr #24
   1243c:	e0283b83 	eor	r3, r8, r3, lsl #23
   12440:	e0266407 	eor	r6, r6, r7, lsl #8
   12444:	e0297c27 	eor	r7, r9, r7, lsr #24
   12448:	e0944002 	adds	r4, r4, r2
   1244c:	e0a55003 	adc	r5, r5, r3
   12450:	e0900006 	adds	r0, r0, r6
   12454:	e0258282 	eor	r8, r5, r2, lsl #5
   12458:	e0a11007 	adc	r1, r1, r7
   1245c:	e0242da2 	eor	r2, r4, r2, lsr #27
   12460:	e0219da6 	eor	r9, r1, r6, lsr #27
   12464:	e0222283 	eor	r2, r2, r3, lsl #5
   12468:	e0206286 	eor	r6, r0, r6, lsl #5
   1246c:	e0283da3 	eor	r3, r8, r3, lsr #27
   12470:	e0266da7 	eor	r6, r6, r7, lsr #27
   12474:	e0297287 	eor	r7, r9, r7, lsl #5
   12478:	e59d8018 	ldr	r8, [sp, #24]
   1247c:	e59d901c 	ldr	r9, [sp, #28]
   12480:	e092200a 	adds	r2, r2, sl
   12484:	e59da020 	ldr	sl, [sp, #32]
   12488:	e0a3300b 	adc	r3, r3, fp
   1248c:	e59db024 	ldr	fp, [sp, #36]	; 0x24
   12490:	e0900008 	adds	r0, r0, r8
   12494:	e59d8000 	ldr	r8, [sp]
   12498:	e0a11009 	adc	r1, r1, r9
   1249c:	e59d9004 	ldr	r9, [sp, #4]
   124a0:	e092200a 	adds	r2, r2, sl
   124a4:	e59da008 	ldr	sl, [sp, #8]
   124a8:	e0a3300b 	adc	r3, r3, fp
   124ac:	e59db00c 	ldr	fp, [sp, #12]
   124b0:	e0944008 	adds	r4, r4, r8
   124b4:	e0a55009 	adc	r5, r5, r9
   124b8:	e096600a 	adds	r6, r6, sl
   124bc:	e0a7700b 	adc	r7, r7, fp
   124c0:	e59da038 	ldr	sl, [sp, #56]	; 0x38
   124c4:	e59db03c 	ldr	fp, [sp, #60]	; 0x3c
   124c8:	e296600d 	adds	r6, r6, #13
   124cc:	e2a77000 	adc	r7, r7, #0
   124d0:	e094400a 	adds	r4, r4, sl
   124d4:	e0a5500b 	adc	r5, r5, fp
   124d8:	e0900002 	adds	r0, r0, r2
   124dc:	e0a11003 	adc	r1, r1, r3
   124e0:	e0944006 	adds	r4, r4, r6
   124e4:	e02183a2 	eor	r8, r1, r2, lsr #7
   124e8:	e0a55007 	adc	r5, r5, r7
   124ec:	e0202c82 	eor	r2, r0, r2, lsl #25
   124f0:	e0259086 	eor	r9, r5, r6, lsl #1
   124f4:	e02223a3 	eor	r2, r2, r3, lsr #7
   124f8:	e0246fa6 	eor	r6, r4, r6, lsr #31
   124fc:	e0283c83 	eor	r3, r8, r3, lsl #25
   12500:	e0266087 	eor	r6, r6, r7, lsl #1
   12504:	e0297fa7 	eor	r7, r9, r7, lsr #31
   12508:	e0944002 	adds	r4, r4, r2
   1250c:	e0a55003 	adc	r5, r5, r3
   12510:	e0900006 	adds	r0, r0, r6
   12514:	e0258a22 	eor	r8, r5, r2, lsr #20
   12518:	e0a11007 	adc	r1, r1, r7
   1251c:	e0242602 	eor	r2, r4, r2, lsl #12
   12520:	e0219706 	eor	r9, r1, r6, lsl #14
   12524:	e0222a23 	eor	r2, r2, r3, lsr #20
   12528:	e0206926 	eor	r6, r0, r6, lsr #18
   1252c:	e0283603 	eor	r3, r8, r3, lsl #12
   12530:	e0266707 	eor	r6, r6, r7, lsl #14
   12534:	e0297927 	eor	r7, r9, r7, lsr #18
   12538:	e0900002 	adds	r0, r0, r2
   1253c:	e0a11003 	adc	r1, r1, r3
   12540:	e0944006 	adds	r4, r4, r6
   12544:	e0218d02 	eor	r8, r1, r2, lsl #26
   12548:	e0a55007 	adc	r5, r5, r7
   1254c:	e0202322 	eor	r2, r0, r2, lsr #6
   12550:	e0259526 	eor	r9, r5, r6, lsr #10
   12554:	e0222d03 	eor	r2, r2, r3, lsl #26
   12558:	e0246b06 	eor	r6, r4, r6, lsl #22
   1255c:	e0283323 	eor	r3, r8, r3, lsr #6
   12560:	e0266527 	eor	r6, r6, r7, lsr #10
   12564:	e0297b07 	eor	r7, r9, r7, lsl #22
   12568:	e0944002 	adds	r4, r4, r2
   1256c:	e0a55003 	adc	r5, r5, r3
   12570:	e0900006 	adds	r0, r0, r6
   12574:	e0248003 	eor	r8, r4, r3
   12578:	e0a11007 	adc	r1, r1, r7
   1257c:	e0223005 	eor	r3, r2, r5
   12580:	e0209007 	eor	r9, r0, r7
   12584:	e1a02008 	mov	r2, r8
   12588:	e0267001 	eor	r7, r6, r1
   1258c:	e1a06009 	mov	r6, r9
   12590:	e59d8020 	ldr	r8, [sp, #32]
   12594:	e59d9024 	ldr	r9, [sp, #36]	; 0x24
   12598:	e092200a 	adds	r2, r2, sl
   1259c:	e59da000 	ldr	sl, [sp]
   125a0:	e0a3300b 	adc	r3, r3, fp
   125a4:	e59db004 	ldr	fp, [sp, #4]
   125a8:	e0900008 	adds	r0, r0, r8
   125ac:	e59d8008 	ldr	r8, [sp, #8]
   125b0:	e0a11009 	adc	r1, r1, r9
   125b4:	e59d900c 	ldr	r9, [sp, #12]
   125b8:	e092200a 	adds	r2, r2, sl
   125bc:	e59da010 	ldr	sl, [sp, #16]
   125c0:	e0a3300b 	adc	r3, r3, fp
   125c4:	e59db014 	ldr	fp, [sp, #20]
   125c8:	e0944008 	adds	r4, r4, r8
   125cc:	e0a55009 	adc	r5, r5, r9
   125d0:	e096600a 	adds	r6, r6, sl
   125d4:	e0a7700b 	adc	r7, r7, fp
   125d8:	e59da028 	ldr	sl, [sp, #40]	; 0x28
   125dc:	e59db02c 	ldr	fp, [sp, #44]	; 0x2c
   125e0:	e296600e 	adds	r6, r6, #14
   125e4:	e2a77000 	adc	r7, r7, #0
   125e8:	e094400a 	adds	r4, r4, sl
   125ec:	e0a5500b 	adc	r5, r5, fp
   125f0:	e0900002 	adds	r0, r0, r2
   125f4:	e0a11003 	adc	r1, r1, r3
   125f8:	e0944006 	adds	r4, r4, r6
   125fc:	e0218922 	eor	r8, r1, r2, lsr #18
   12600:	e0a55007 	adc	r5, r5, r7
   12604:	e0202702 	eor	r2, r0, r2, lsl #14
   12608:	e0259826 	eor	r9, r5, r6, lsr #16
   1260c:	e0222923 	eor	r2, r2, r3, lsr #18
   12610:	e0246806 	eor	r6, r4, r6, lsl #16
   12614:	e0283703 	eor	r3, r8, r3, lsl #14
   12618:	e0266827 	eor	r6, r6, r7, lsr #16
   1261c:	e0297807 	eor	r7, r9, r7, lsl #16
   12620:	e0944002 	adds	r4, r4, r2
   12624:	e0a55003 	adc	r5, r5, r3
   12628:	e0900006 	adds	r0, r0, r6
   1262c:	e0258c82 	eor	r8, r5, r2, lsl #25
   12630:	e0a11007 	adc	r1, r1, r7
   12634:	e02423a2 	eor	r2, r4, r2, lsr #7
   12638:	e0219a06 	eor	r9, r1, r6, lsl #20
   1263c:	e0222c83 	eor	r2, r2, r3, lsl #25
   12640:	e0206626 	eor	r6, r0, r6, lsr #12
   12644:	e02833a3 	eor	r3, r8, r3, lsr #7
   12648:	e0266a07 	eor	r6, r6, r7, lsl #20
   1264c:	e0297627 	eor	r7, r9, r7, lsr #12
   12650:	e0900002 	adds	r0, r0, r2
   12654:	e0a11003 	adc	r1, r1, r3
   12658:	e0944006 	adds	r4, r4, r6
   1265c:	e02184a2 	eor	r8, r1, r2, lsr #9
   12660:	e0a55007 	adc	r5, r5, r7
   12664:	e0202b82 	eor	r2, r0, r2, lsl #23
   12668:	e0259406 	eor	r9, r5, r6, lsl #8
   1266c:	e02224a3 	eor	r2, r2, r3, lsr #9
   12670:	e0246c26 	eor	r6, r4, r6, lsr #24
   12674:	e0283b83 	eor	r3, r8, r3, lsl #23
   12678:	e0266407 	eor	r6, r6, r7, lsl #8
   1267c:	e0297c27 	eor	r7, r9, r7, lsr #24
   12680:	e0944002 	adds	r4, r4, r2
   12684:	e0a55003 	adc	r5, r5, r3
   12688:	e0900006 	adds	r0, r0, r6
   1268c:	e0258282 	eor	r8, r5, r2, lsl #5
   12690:	e0a11007 	adc	r1, r1, r7
   12694:	e0242da2 	eor	r2, r4, r2, lsr #27
   12698:	e0219da6 	eor	r9, r1, r6, lsr #27
   1269c:	e0222283 	eor	r2, r2, r3, lsl #5
   126a0:	e0206286 	eor	r6, r0, r6, lsl #5
   126a4:	e0283da3 	eor	r3, r8, r3, lsr #27
   126a8:	e0266da7 	eor	r6, r6, r7, lsr #27
   126ac:	e0297287 	eor	r7, r9, r7, lsl #5
   126b0:	e59d8000 	ldr	r8, [sp]
   126b4:	e59d9004 	ldr	r9, [sp, #4]
   126b8:	e092200a 	adds	r2, r2, sl
   126bc:	e59da008 	ldr	sl, [sp, #8]
   126c0:	e0a3300b 	adc	r3, r3, fp
   126c4:	e59db00c 	ldr	fp, [sp, #12]
   126c8:	e0900008 	adds	r0, r0, r8
   126cc:	e59d8010 	ldr	r8, [sp, #16]
   126d0:	e0a11009 	adc	r1, r1, r9
   126d4:	e59d9014 	ldr	r9, [sp, #20]
   126d8:	e092200a 	adds	r2, r2, sl
   126dc:	e59da018 	ldr	sl, [sp, #24]
   126e0:	e0a3300b 	adc	r3, r3, fp
   126e4:	e59db01c 	ldr	fp, [sp, #28]
   126e8:	e0944008 	adds	r4, r4, r8
   126ec:	e0a55009 	adc	r5, r5, r9
   126f0:	e096600a 	adds	r6, r6, sl
   126f4:	e0a7700b 	adc	r7, r7, fp
   126f8:	e59da030 	ldr	sl, [sp, #48]	; 0x30
   126fc:	e59db034 	ldr	fp, [sp, #52]	; 0x34
   12700:	e296600f 	adds	r6, r6, #15
   12704:	e2a77000 	adc	r7, r7, #0
   12708:	e094400a 	adds	r4, r4, sl
   1270c:	e0a5500b 	adc	r5, r5, fp
   12710:	e0900002 	adds	r0, r0, r2
   12714:	e0a11003 	adc	r1, r1, r3
   12718:	e0944006 	adds	r4, r4, r6
   1271c:	e02183a2 	eor	r8, r1, r2, lsr #7
   12720:	e0a55007 	adc	r5, r5, r7
   12724:	e0202c82 	eor	r2, r0, r2, lsl #25
   12728:	e0259086 	eor	r9, r5, r6, lsl #1
   1272c:	e02223a3 	eor	r2, r2, r3, lsr #7
   12730:	e0246fa6 	eor	r6, r4, r6, lsr #31
   12734:	e0283c83 	eor	r3, r8, r3, lsl #25
   12738:	e0266087 	eor	r6, r6, r7, lsl #1
   1273c:	e0297fa7 	eor	r7, r9, r7, lsr #31
   12740:	e0944002 	adds	r4, r4, r2
   12744:	e0a55003 	adc	r5, r5, r3
   12748:	e0900006 	adds	r0, r0, r6
   1274c:	e0258a22 	eor	r8, r5, r2, lsr #20
   12750:	e0a11007 	adc	r1, r1, r7
   12754:	e0242602 	eor	r2, r4, r2, lsl #12
   12758:	e0219706 	eor	r9, r1, r6, lsl #14
   1275c:	e0222a23 	eor	r2, r2, r3, lsr #20
   12760:	e0206926 	eor	r6, r0, r6, lsr #18
   12764:	e0283603 	eor	r3, r8, r3, lsl #12
   12768:	e0266707 	eor	r6, r6, r7, lsl #14
   1276c:	e0297927 	eor	r7, r9, r7, lsr #18
   12770:	e0900002 	adds	r0, r0, r2
   12774:	e0a11003 	adc	r1, r1, r3
   12778:	e0944006 	adds	r4, r4, r6
   1277c:	e0218d02 	eor	r8, r1, r2, lsl #26
   12780:	e0a55007 	adc	r5, r5, r7
   12784:	e0202322 	eor	r2, r0, r2, lsr #6
   12788:	e0259526 	eor	r9, r5, r6, lsr #10
   1278c:	e0222d03 	eor	r2, r2, r3, lsl #26
   12790:	e0246b06 	eor	r6, r4, r6, lsl #22
   12794:	e0283323 	eor	r3, r8, r3, lsr #6
   12798:	e0266527 	eor	r6, r6, r7, lsr #10
   1279c:	e0297b07 	eor	r7, r9, r7, lsl #22
   127a0:	e0944002 	adds	r4, r4, r2
   127a4:	e0a55003 	adc	r5, r5, r3
   127a8:	e0900006 	adds	r0, r0, r6
   127ac:	e0248003 	eor	r8, r4, r3
   127b0:	e0a11007 	adc	r1, r1, r7
   127b4:	e0223005 	eor	r3, r2, r5
   127b8:	e0209007 	eor	r9, r0, r7
   127bc:	e1a02008 	mov	r2, r8
   127c0:	e0267001 	eor	r7, r6, r1
   127c4:	e1a06009 	mov	r6, r9
   127c8:	e59d8008 	ldr	r8, [sp, #8]
   127cc:	e59d900c 	ldr	r9, [sp, #12]
   127d0:	e092200a 	adds	r2, r2, sl
   127d4:	e59da010 	ldr	sl, [sp, #16]
   127d8:	e0a3300b 	adc	r3, r3, fp
   127dc:	e59db014 	ldr	fp, [sp, #20]
   127e0:	e0900008 	adds	r0, r0, r8
   127e4:	e59d8018 	ldr	r8, [sp, #24]
   127e8:	e0a11009 	adc	r1, r1, r9
   127ec:	e59d901c 	ldr	r9, [sp, #28]
   127f0:	e092200a 	adds	r2, r2, sl
   127f4:	e59da020 	ldr	sl, [sp, #32]
   127f8:	e0a3300b 	adc	r3, r3, fp
   127fc:	e59db024 	ldr	fp, [sp, #36]	; 0x24
   12800:	e0944008 	adds	r4, r4, r8
   12804:	e0a55009 	adc	r5, r5, r9
   12808:	e096600a 	adds	r6, r6, sl
   1280c:	e0a7700b 	adc	r7, r7, fp
   12810:	e59da038 	ldr	sl, [sp, #56]	; 0x38
   12814:	e59db03c 	ldr	fp, [sp, #60]	; 0x3c
   12818:	e2966010 	adds	r6, r6, #16
   1281c:	e2a77000 	adc	r7, r7, #0
   12820:	e094400a 	adds	r4, r4, sl
   12824:	e0a5500b 	adc	r5, r5, fp
   12828:	e0900002 	adds	r0, r0, r2
   1282c:	e0a11003 	adc	r1, r1, r3
   12830:	e0944006 	adds	r4, r4, r6
   12834:	e0218922 	eor	r8, r1, r2, lsr #18
   12838:	e0a55007 	adc	r5, r5, r7
   1283c:	e0202702 	eor	r2, r0, r2, lsl #14
   12840:	e0259826 	eor	r9, r5, r6, lsr #16
   12844:	e0222923 	eor	r2, r2, r3, lsr #18
   12848:	e0246806 	eor	r6, r4, r6, lsl #16
   1284c:	e0283703 	eor	r3, r8, r3, lsl #14
   12850:	e0266827 	eor	r6, r6, r7, lsr #16
   12854:	e0297807 	eor	r7, r9, r7, lsl #16
   12858:	e0944002 	adds	r4, r4, r2
   1285c:	e0a55003 	adc	r5, r5, r3
   12860:	e0900006 	adds	r0, r0, r6
   12864:	e0258c82 	eor	r8, r5, r2, lsl #25
   12868:	e0a11007 	adc	r1, r1, r7
   1286c:	e02423a2 	eor	r2, r4, r2, lsr #7
   12870:	e0219a06 	eor	r9, r1, r6, lsl #20
   12874:	e0222c83 	eor	r2, r2, r3, lsl #25
   12878:	e0206626 	eor	r6, r0, r6, lsr #12
   1287c:	e02833a3 	eor	r3, r8, r3, lsr #7
   12880:	e0266a07 	eor	r6, r6, r7, lsl #20
   12884:	e0297627 	eor	r7, r9, r7, lsr #12
   12888:	e0900002 	adds	r0, r0, r2
   1288c:	e0a11003 	adc	r1, r1, r3
   12890:	e0944006 	adds	r4, r4, r6
   12894:	e02184a2 	eor	r8, r1, r2, lsr #9
   12898:	e0a55007 	adc	r5, r5, r7
   1289c:	e0202b82 	eor	r2, r0, r2, lsl #23
   128a0:	e0259406 	eor	r9, r5, r6, lsl #8
   128a4:	e02224a3 	eor	r2, r2, r3, lsr #9
   128a8:	e0246c26 	eor	r6, r4, r6, lsr #24
   128ac:	e0283b83 	eor	r3, r8, r3, lsl #23
   128b0:	e0266407 	eor	r6, r6, r7, lsl #8
   128b4:	e0297c27 	eor	r7, r9, r7, lsr #24
   128b8:	e0944002 	adds	r4, r4, r2
   128bc:	e0a55003 	adc	r5, r5, r3
   128c0:	e0900006 	adds	r0, r0, r6
   128c4:	e0258282 	eor	r8, r5, r2, lsl #5
   128c8:	e0a11007 	adc	r1, r1, r7
   128cc:	e0242da2 	eor	r2, r4, r2, lsr #27
   128d0:	e0219da6 	eor	r9, r1, r6, lsr #27
   128d4:	e0222283 	eor	r2, r2, r3, lsl #5
   128d8:	e0206286 	eor	r6, r0, r6, lsl #5
   128dc:	e0283da3 	eor	r3, r8, r3, lsr #27
   128e0:	e0266da7 	eor	r6, r6, r7, lsr #27
   128e4:	e0297287 	eor	r7, r9, r7, lsl #5
   128e8:	e59d8010 	ldr	r8, [sp, #16]
   128ec:	e59d9014 	ldr	r9, [sp, #20]
   128f0:	e092200a 	adds	r2, r2, sl
   128f4:	e59da018 	ldr	sl, [sp, #24]
   128f8:	e0a3300b 	adc	r3, r3, fp
   128fc:	e59db01c 	ldr	fp, [sp, #28]
   12900:	e0900008 	adds	r0, r0, r8
   12904:	e59d8020 	ldr	r8, [sp, #32]
   12908:	e0a11009 	adc	r1, r1, r9
   1290c:	e59d9024 	ldr	r9, [sp, #36]	; 0x24
   12910:	e092200a 	adds	r2, r2, sl
   12914:	e59da000 	ldr	sl, [sp]
   12918:	e0a3300b 	adc	r3, r3, fp
   1291c:	e59db004 	ldr	fp, [sp, #4]
   12920:	e0944008 	adds	r4, r4, r8
   12924:	e0a55009 	adc	r5, r5, r9
   12928:	e096600a 	adds	r6, r6, sl
   1292c:	e0a7700b 	adc	r7, r7, fp
   12930:	e59da028 	ldr	sl, [sp, #40]	; 0x28
   12934:	e59db02c 	ldr	fp, [sp, #44]	; 0x2c
   12938:	e2966011 	adds	r6, r6, #17
   1293c:	e2a77000 	adc	r7, r7, #0
   12940:	e094400a 	adds	r4, r4, sl
   12944:	e0a5500b 	adc	r5, r5, fp
   12948:	e0900002 	adds	r0, r0, r2
   1294c:	e0a11003 	adc	r1, r1, r3
   12950:	e0944006 	adds	r4, r4, r6
   12954:	e02183a2 	eor	r8, r1, r2, lsr #7
   12958:	e0a55007 	adc	r5, r5, r7
   1295c:	e0202c82 	eor	r2, r0, r2, lsl #25
   12960:	e0259086 	eor	r9, r5, r6, lsl #1
   12964:	e02223a3 	eor	r2, r2, r3, lsr #7
   12968:	e0246fa6 	eor	r6, r4, r6, lsr #31
   1296c:	e0283c83 	eor	r3, r8, r3, lsl #25
   12970:	e0266087 	eor	r6, r6, r7, lsl #1
   12974:	e0297fa7 	eor	r7, r9, r7, lsr #31
   12978:	e0944002 	adds	r4, r4, r2
   1297c:	e0a55003 	adc	r5, r5, r3
   12980:	e0900006 	adds	r0, r0, r6
   12984:	e0258a22 	eor	r8, r5, r2, lsr #20
   12988:	e0a11007 	adc	r1, r1, r7
   1298c:	e0242602 	eor	r2, r4, r2, lsl #12
   12990:	e0219706 	eor	r9, r1, r6, lsl #14
   12994:	e0222a23 	eor	r2, r2, r3, lsr #20
   12998:	e0206926 	eor	r6, r0, r6, lsr #18
   1299c:	e0283603 	eor	r3, r8, r3, lsl #12
   129a0:	e0266707 	eor	r6, r6, r7, lsl #14
   129a4:	e0297927 	eor	r7, r9, r7, lsr #18
   129a8:	e0900002 	adds	r0, r0, r2
   129ac:	e0a11003 	adc	r1, r1, r3
   129b0:	e0944006 	adds	r4, r4, r6
   129b4:	e0218d02 	eor	r8, r1, r2, lsl #26
   129b8:	e0a55007 	adc	r5, r5, r7
   129bc:	e0202322 	eor	r2, r0, r2, lsr #6
   129c0:	e0259526 	eor	r9, r5, r6, lsr #10
   129c4:	e0222d03 	eor	r2, r2, r3, lsl #26
   129c8:	e0246b06 	eor	r6, r4, r6, lsl #22
   129cc:	e0283323 	eor	r3, r8, r3, lsr #6
   129d0:	e0266527 	eor	r6, r6, r7, lsr #10
   129d4:	e0297b07 	eor	r7, r9, r7, lsl #22
   129d8:	e0944002 	adds	r4, r4, r2
   129dc:	e0a55003 	adc	r5, r5, r3
   129e0:	e0900006 	adds	r0, r0, r6
   129e4:	e0248003 	eor	r8, r4, r3
   129e8:	e0a11007 	adc	r1, r1, r7
   129ec:	e0223005 	eor	r3, r2, r5
   129f0:	e0209007 	eor	r9, r0, r7
   129f4:	e1a02008 	mov	r2, r8
   129f8:	e0267001 	eor	r7, r6, r1
   129fc:	e1a06009 	mov	r6, r9
   12a00:	e59d8018 	ldr	r8, [sp, #24]
   12a04:	e59d901c 	ldr	r9, [sp, #28]
   12a08:	e092200a 	adds	r2, r2, sl
   12a0c:	e59da020 	ldr	sl, [sp, #32]
   12a10:	e0a3300b 	adc	r3, r3, fp
   12a14:	e59db024 	ldr	fp, [sp, #36]	; 0x24
   12a18:	e0900008 	adds	r0, r0, r8
   12a1c:	e59d8000 	ldr	r8, [sp]
   12a20:	e0a11009 	adc	r1, r1, r9
   12a24:	e59d9004 	ldr	r9, [sp, #4]
   12a28:	e092200a 	adds	r2, r2, sl
   12a2c:	e59da008 	ldr	sl, [sp, #8]
   12a30:	e0a3300b 	adc	r3, r3, fp
   12a34:	e59db00c 	ldr	fp, [sp, #12]
   12a38:	e0944008 	adds	r4, r4, r8
   12a3c:	e0a55009 	adc	r5, r5, r9
   12a40:	e096600a 	adds	r6, r6, sl
   12a44:	e0a7700b 	adc	r7, r7, fp
   12a48:	e59da030 	ldr	sl, [sp, #48]	; 0x30
   12a4c:	e59db034 	ldr	fp, [sp, #52]	; 0x34
   12a50:	e2966012 	adds	r6, r6, #18
   12a54:	e2a77000 	adc	r7, r7, #0
   12a58:	e094400a 	adds	r4, r4, sl
   12a5c:	e0a5500b 	adc	r5, r5, fp
   12a60:	e59c8000 	ldr	r8, [ip]
   12a64:	e59c9004 	ldr	r9, [ip, #4]
   12a68:	e59ca008 	ldr	sl, [ip, #8]
   12a6c:	e0200008 	eor	r0, r0, r8
   12a70:	e59cb00c 	ldr	fp, [ip, #12]
   12a74:	e0211009 	eor	r1, r1, r9
   12a78:	e59c8010 	ldr	r8, [ip, #16]
   12a7c:	e022200a 	eor	r2, r2, sl
   12a80:	e59c9014 	ldr	r9, [ip, #20]
   12a84:	e023300b 	eor	r3, r3, fp
   12a88:	e59ca018 	ldr	sl, [ip, #24]
   12a8c:	e0244008 	eor	r4, r4, r8
   12a90:	e59cb01c 	ldr	fp, [ip, #28]
   12a94:	e0255009 	eor	r5, r5, r9
   12a98:	e28cc020 	add	ip, ip, #32
   12a9c:	e026600a 	eor	r6, r6, sl
   12aa0:	e58dc044 	str	ip, [sp, #68]	; 0x44
   12aa4:	e027700b 	eor	r7, r7, fp
   12aa8:	e59dc048 	ldr	ip, [sp, #72]	; 0x48
   12aac:	e1cda3d0 	ldrd	sl, [sp, #48]	; 0x30
   12ab0:	e1cd82d8 	ldrd	r8, [sp, #40]	; 0x28
   12ab4:	e3cbb101 	bic	fp, fp, #1073741824	; 0x40000000
` : term quotation;

fun drop 0 xs = xs
  | drop _ [] = []
  | drop n xs = drop (n-1) (tl xs)

fun take 0 xs = []
  | take _ [] = []
  | take n xs = hd xs :: take (n-1) (tl xs)

val code = 
  quote_to_strings skein_qcode
  |> map (fn line => let val ts = String.tokens (fn c => mem c [#"\t"]) line in 
                     el 2 ts ^ "\n" end)

val n = length code div 7 + 1

fun chunks name i n [] = []
  | chunks name i n xs = let
      val (xs,ys) = (take n xs,drop n xs)
      in (name ^ int_to_string i, xs) :: chunks name (i+1) n ys end

val xs = chunks "Skein_256_" 0 n code
         |> map (fn (n,x) => (n,x |> concat |> (fn str => [(QUOTE str):term frag])))

val _ = map (fn (x,y) => f x y) xs 

val _ = f "Skein_256_body" `
  insert: Skein_256_0
  insert: Skein_256_1
  insert: Skein_256_2
  insert: Skein_256_3
  insert: Skein_256_4
  insert: Skein_256_5
  insert: Skein_256_6`;

val _ = f "Skein_256_block" `
  insert: Skein_256_body
   e25cc001 	(* subs	ip, ip, #1                           *)
   e58dc048 	(* str	ip, [sp, #72]	; 0x48               *)
   1afffab7 	(* bne	115a4 <Skein_256_Process_Block+0x14> *)`;

in () end;

val _ = benchmark "256-bit Skein block cipher" do_skein;

(*
val _ = compare_it do_skein fast_decompile do_skein old_decompile;
*)


val _ = export_theory();

