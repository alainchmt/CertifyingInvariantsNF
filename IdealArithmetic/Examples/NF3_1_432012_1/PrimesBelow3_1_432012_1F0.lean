
import IdealArithmetic.Examples.NF3_1_432012_1.RI3_1_432012_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-520918563075836544328613, 35573486342601338769369, -12247834338553075611402]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-520918563075836544328613, 35573486342601338769369, -12247834338553075611402]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-520918563075836544328613, 35573486342601338769369, -12247834338553075611402], ![992074581422799124523562, -67748692549372746706739, 23325652004048263157967], ![-1889377812327909315795327, 129025457273013387678783, -44423040545324483548772]]]
  hmulB := by decide  
  f := ![![![168695739653, 120937118898, 16990725255]], ![![-603776503001, -169511987942, 77459284704]], ![![-5501729818370, -3179320930209, -152521262687]]]
  g := ![![![-272122107539942403743290, 35573486342601338769369, -12247834338553075611402], ![518248810984061804036167, -67748692549372746706739, 23325652004048263157967], ![-986990114527799109962669, 129025457273013387678783, -44423040545324483548772]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-520918563075836544328613, 35573486342601338769369, -12247834338553075611402]] ![![-520918563075836544328613, 35573486342601338769369, -12247834338553075611402]]
  ![![329788487378410237108879214289034615912874394601, -22521229004455919872616686357402675696862016654, 7753985068842200270767376823484717212591856593]] where
 M := ![![![329788487378410237108879214289034615912874394601, -22521229004455919872616686357402675696862016654, 7753985068842200270767376823484717212591856593]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![329788487378410237108879214289034615912874394601, -22521229004455919872616686357402675696862016654, 7753985068842200270767376823484717212591856593]] ![![-520918563075836544328613, 35573486342601338769369, -12247834338553075611402]]
  ![![2, 0, 0]] where
 M := ![![![-208785891148030076587719560258330876886900094276527540924522481959960872, 14257971540555413821510501464064954245875751244884573993933061594574394, -4908972703735205288569997737313643400835197571489600692003477614876816]]]
 hmul := by decide  
 g := ![![![![-104392945574015038293859780129165438443450047138263770462261240979980436, 7128985770277706910755250732032477122937875622442286996966530797287197, -2454486351867602644284998868656821700417598785744800346001738807438408]]]]
 hle2 := by decide  

def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![218554896, 145337152, 16056075]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![218554896, 145337152, 16056075]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![218554896, 145337152, 16056075], ![-1300542075, -375519879, 161393227], ![-13072851387, -7272091474, -214126652]]]
  hmulB := by decide  
  f := ![![![1254075124477761706, -85640688344429446, 29485807305484429]], ![![-796116797248079583, 54366751391612611, -18718293679648339]], ![![1516181788051515459, -103539931101091040, 35648457711964272]]]
  g := ![![![72851632, 145337152, 16056075], ![-433514025, -375519879, 161393227], ![-4357617129, -7272091474, -214126652]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1015813231, 69369803, -23883795]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-1015813231, 69369803, -23883795]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![-1015813231, 69369803, -23883795], ![1934587395, -132112816, 45486008], ![-3684366648, 251605099, -86626808]]]
  hmulB := by decide  
  f := ![![![-16536, -8119, 296]], ![![-13504, -11869, -2509]], ![![200197, 83079, -11573]]]
  g := ![![![-345805148, 69369803, -23883795], ![658576065, -132112816, 45486008], ![-1254239377, 251605099, -86626808]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![218554896, 145337152, 16056075]] ![![-1015813231, 69369803, -23883795]]
  ![![-16536, -8119, 296]] where
 M := ![![![-16536, -8119, 296]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-16536, -8119, 296]] ![![-1015813231, 69369803, -23883795]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, -3, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![43, -3, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![3, 2, 1]] where
  M :=![![![43, -3, 1], ![-81, 6, -2], ![162, -7, 4]]]
  hmulB := by decide  
  f := ![![![2, 1, 0]], ![![0, 2, 1]], ![![-15, -6, 1]]]
  g := ![![![8, -1, 1], ![-15, 2, -2], ![30, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4], [0, 1]]
 g := ![![[1, 1], [1]], ![[0, 4], [1]]]
 h' := ![![[4, 4], [4, 4], [0, 1]], ![[0, 1], [0, 1], [4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-242, -193, -34]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -25, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 1, 0], ![0, 2, 1], ![-81, -37, 3]]]
  hmulB := by decide  
  f := ![![![43, -3, 1]], ![![1, 0, 0]], ![![41, -2, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 1], ![-2, -37, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![43, -3, 1]] ![![2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-120806615119699962706279104638117179402, 8249873929777582316175585275631820970, -2840404458329928851843759566948484623]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-120806615119699962706279104638117179402, 8249873929777582316175585275631820970, -2840404458329928851843759566948484623]] 
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![-120806615119699962706279104638117179402, 8249873929777582316175585275631820970, -2840404458329928851843759566948484623], ![230072761124724236999344524922827254463, -15711650161492595188060000661023248351, 5409469471447653464331825708683336347], ![-438167027187259930610877882403350244107, 29922390681161058819066973701543809624, -10302180690044941723728174952339912004]]]
  hmulB := by decide  
  f := ![![![6255787731349498124, 3977309901121487872, 363628753835810083]], ![![-3314020189907302657, -460166608493426725, 672081058399015434]], ![![-44868757809063449373, -23743542841055959118, -96537854657616642]]]
  g := ![![![-16002008899928281701627447501722584662, 8249873929777582316175585275631820970, -2840404458329928851843759566948484623], ![30475370636790130200201938761678640676, -15711650161492595188060000661023248351, 5409469471447653464331825708683336347], ![-58039476246878762726796543770122083101, 29922390681161058819066973701543809624, -10302180690044941723728174952339912004]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-112, -55, 2]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-112, -55, 2]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![-112, -55, 2], ![-162, -186, -53], ![4293, 1799, -239]]]
  hmulB := by decide  
  f := ![![![-139801, 9547, -3287]], ![![-41851, 2858, -984]], ![![-172295, 11766, -4051]]]
  g := ![![![14, -55, 2], ![121, -186, -53], ![-244, 1799, -239]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-120806615119699962706279104638117179402, 8249873929777582316175585275631820970, -2840404458329928851843759566948484623]] ![![-120806615119699962706279104638117179402, 8249873929777582316175585275631820970, -2840404458329928851843759566948484623]]
  ![![17736881108149991597198895889830036407797348251124563423919573355127288433375, -1211250169576430314406487945527936704889234247750235080363055740277318792162, 417029449310691434858410723379216731265590019063611239835495911954494246528]] where
 M := ![![![17736881108149991597198895889830036407797348251124563423919573355127288433375, -1211250169576430314406487945527936704889234247750235080363055740277318792162, 417029449310691434858410723379216731265590019063611239835495911954494246528]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![17736881108149991597198895889830036407797348251124563423919573355127288433375, -1211250169576430314406487945527936704889234247750235080363055740277318792162, 417029449310691434858410723379216731265590019063611239835495911954494246528]] ![![-112, -55, 2]]
  ![![7, 0, 0]] where
 M := ![![![-730750619018105268057018460904158069104150329967846393235828686859863052, 49902900391943948375286755124227339860565129357096008978765715581010379, -17181404463073218509994992080597751902923191500213602422012171652068856]]]
 hmul := by decide  
 g := ![![![![-104392945574015038293859780129165438443450047138263770462261240979980436, 7128985770277706910755250732032477122937875622442286996966530797287197, -2454486351867602644284998868656821700417598785744800346001738807438408]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10295341, -703068, 242064]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![10295341, -703068, 242064]] 
 ![![11, 0, 0], ![0, 11, 0], ![5, 7, 1]] where
  M :=![![![10295341, -703068, 242064], ![-19607184, 1338973, -461004], ![37341324, -2550036, 877969]]]
  hmulB := by decide  
  f := ![![![-937, -492, 0]], ![![0, -937, -492]], ![![3197, 835, -443]]]
  g := ![![![825911, -217956, 242064], ![-1572924, 415091, -461004], ![2995589, -790529, 877969]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10], [0, 1]]
 g := ![![[6, 1], [9, 9], [1]], ![[3, 10], [4, 2], [1]]]
 h' := ![![[8, 10], [1, 10], [5, 8], [0, 1]], ![[0, 1], [4, 1], [3, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [9, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [6, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![247, -620, -329]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![172, 153, -329]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![937, 492, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![937, 492, 0]] 
 ![![11, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![937, 492, 0], ![0, 937, 492], ![-39852, -18204, 1429]]]
  hmulB := by decide  
  f := ![![![-10295341, 703068, -242064]], ![![-1025349, 70021, -24108]], ![![-5266546, 359652, -123827]]]
  g := ![![![-49, 492, 0], ![-345, 937, 492], ![1082, -18204, 1429]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![10295341, -703068, 242064]] ![![937, 492, 0]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [5, 9, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 9], [5, 3], [0, 1]]
 g := ![![[9], [4, 1], [1]], ![[9], [11, 9], [1]], ![[9], [9, 3], [1]]]
 h' := ![![[7, 9], [5, 10], [8, 4, 12], [0, 1]], ![[5, 3], [10, 12], [0, 1, 10], [7, 9]], ![[0, 1], [3, 4], [3, 8, 4], [5, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10], []]
 b := ![[], [6, 10, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [5, 9, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-277654, 16029, -6552]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21358, 1233, -504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [4, 6, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 12, 12], [0, 4, 5], [0, 1]]
 g := ![![[8], [4, 4], [2, 1], []], ![[8, 16, 15, 3], [3, 16], [1, 16], [15, 8]], ![[0, 13, 14, 14], [6, 4], [7, 8], [5, 8]]]
 h' := ![![[2, 12, 12], [14, 12], [9, 1, 15], [0, 0, 1], [0, 1]], ![[0, 4, 5], [4, 8, 8], [4, 7, 4], [12, 11, 4], [2, 12, 12]], ![[0, 1], [14, 14, 9], [15, 9, 15], [14, 6, 12], [0, 4, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 3], []]
 b := ![[], [12, 9, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [4, 6, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-261766, -212857, -39491]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15398, -12521, -2323]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229074442882080696234325564330852, -15643475089825817966688781842280, 5385997018515939740336797581309]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![229074442882080696234325564330852, -15643475089825817966688781842280, 5385997018515939740336797581309]] 
 ![![19, 0, 0], ![0, 19, 0], ![17, 11, 1]] where
  M :=![![![229074442882080696234325564330852, -15643475089825817966688781842280, 5385997018515939740336797581309], ![-436265758499791118967280604086029, 29792553196990925841864053822419, -10257478071309878226351984260971], ![830855723776100136334510725138651, -56739069861325624592257186430102, 19535075125681047615512069561448]]]
  hmulB := by decide  
  f := ![![![-686771411455070, -1007062351881162, -339439248311189]], ![![27494579113206309, 11872480776058923, -1346501600192351]], ![![21043783466637560, 10041703519736405, -529263455133658]]]
  g := ![![![7237499661437353718347368707821, -3941549594394797637389134486141, 5385997018515939740336797581309], ![-13783612173027536269436677455238, 7506569051652609806933467404900, -10257478071309878226351984260971], ![26250497191553806677410818031265, -14296047170727218334888944821370, 19535075125681047615512069561448]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [5, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 18], [0, 1]]
 g := ![![[0, 4], [], [], [1]], ![[0, 15], [], [], [1]]]
 h' := ![![[0, 18], [0, 17], [6], [14], [0, 1]], ![[0, 1], [0, 2], [6], [14], [0, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [5, 0, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-238, -192, -33]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 9, -33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-686771411455070, -1007062351881162, -339439248311189]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-686771411455070, -1007062351881162, -339439248311189]] 
 ![![19, 0, 0], ![7, 1, 0], ![8, 0, 1]] where
  M :=![![![-686771411455070, -1007062351881162, -339439248311189], ![27494579113206309, 11872480776058923, -1346501600192351], ![109066629615580431, 77315138320323296, 10525979175866572]]]
  hmulB := by decide  
  f := ![![![229074442882080696234325564330852, -15643475089825817966688781842280, 5385997018515939740336797581309]], ![![61434491667093355509105176117365, -4195356443778410522366179951239, 1444447424121142102947663095168]], ![![140181645622776089800479749462393, -9572993188417482543461444272018, 3295950067042556080958234221680]]]
  g := ![![![477798896747504, -1007062351881162, -339439248311189], ![-2360040711456176, 11872480776058923, -1346501600192351], ![-27176166949137643, 77315138320323296, 10525979175866572]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![229074442882080696234325564330852, -15643475089825817966688781842280, 5385997018515939740336797581309]] ![![-686771411455070, -1007062351881162, -339439248311189]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691906785874623710431, -47250258183025854587, 16268108475680082997]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![691906785874623710431, -47250258183025854587, 16268108475680082997]] 
 ![![23, 0, 0], ![0, 23, 0], ![21, 5, 1]] where
  M :=![![![691906785874623710431, -47250258183025854587, 16268108475680082997], ![-1317716786530086722757, 89986772274460639542, -30982149707345771590], ![2509554126295007498790, -171377247358293173927, 59004622567114867952]]]
  hmulB := by decide  
  f := ![![![2561496698, 2371394635, 538944172]], ![![-43654477932, -17379437666, 2910338807]], ![![-17400800103, -8192822382, 495670556]]]
  g := ![![![15229413386319215978, -5590904372235924764, 16268108475680082997], ![-29003984464166326929, 10647718296138673804, -30982149707345771590], ![55237263147199794426, -20278276530168152769, 59004622567114867952]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [5, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 22], [0, 1]]
 g := ![![[22, 1], [19, 1], [6, 2], [1]], ![[4, 22], [1, 22], [16, 21], [1]]]
 h' := ![![[5, 22], [20, 1], [16, 22], [18, 5], [0, 1]], ![[0, 1], [2, 22], [11, 1], [20, 18], [5, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [1, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [5, 18, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3135, -1144, 383]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-486, -133, 383]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2561496698, -2371394635, -538944172]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-2561496698, -2371394635, -538944172]] 
 ![![23, 0, 0], ![17, 1, 0], ![10, 0, 1]] where
  M :=![![![-2561496698, -2371394635, -538944172], ![43654477932, 17379437666, -2910338807], ![235737443367, 151337013791, 14469098859]]]
  hmulB := by decide  
  f := ![![![-691906785874623710431, 47250258183025854587, -16268108475680082997]], ![![-454117329275587667590, 31011635514651256019, -10677204103444158233]], ![![-409940086306141069700, 27994775182110944339, -9638509014083291214]]]
  g := ![![![1875724079, -2371394635, -538944172], ![-9682285840, 17379437666, -2910338807], ![-107899251290, 151337013791, 14469098859]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![691906785874623710431, -47250258183025854587, 16268108475680082997]] ![![-2561496698, -2371394635, -538944172]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [8, 5, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 28, 13], [28, 0, 16], [0, 1]]
 g := ![![[27, 26, 28], [2, 9], [26, 6, 22], [1]], ![[22, 27, 10, 20], [19, 9], [17, 19, 19, 28], [7, 21, 26, 22]], ![[27, 4, 21, 24], [], [5, 5, 27, 9], [8, 18, 18, 7]]]
 h' := ![![[16, 28, 13], [9, 14, 17], [24, 2, 3], [21, 24, 15], [0, 1]], ![[28, 0, 16], [22, 7, 8], [0, 0, 26], [9, 15, 22], [16, 28, 13]], ![[0, 1], [4, 8, 4], [27, 27], [22, 19, 21], [28, 0, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 26], []]
 b := ![[], [21, 12, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [8, 5, 14, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18241, 5916, -1827]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![629, 204, -63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [12, 25, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 6, 25], [30, 24, 6], [0, 1]]
 g := ![![[12, 19, 8], [6, 7, 4], [2, 4, 7], [1]], ![[20, 20, 1, 1], [19, 28, 15, 18], [13, 2, 13, 9], [0, 27, 7, 1]], ![[5, 19, 19, 21], [20, 12, 23, 21], [18, 25, 12, 23], [30, 21, 9, 30]]]
 h' := ![![[11, 6, 25], [21, 1, 16], [7, 15, 2], [19, 6, 10], [0, 1]], ![[30, 24, 6], [23, 7, 6], [12, 1, 20], [29, 25, 18], [11, 6, 25]], ![[0, 1], [23, 23, 9], [4, 15, 9], [11, 0, 3], [30, 24, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 23], []]
 b := ![[], [30, 21, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [12, 25, 21, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![120621, 70184, 3844]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3891, 2264, 124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB186I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB186I0 : PrimesBelowBoundCertificateInterval O 1 31 186 where
  m := 11
  g := ![3, 3, 2, 3, 2, 1, 1, 2, 2, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB186I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![529, 23]
    · exact ![24389]
    · exact ![29791]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I19N1, I23N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1, I3N1], [I5N0, I5N1], [I7N0, I7N0, I7N1], [I11N0, I11N1], [], [], [I19N1], [I23N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
