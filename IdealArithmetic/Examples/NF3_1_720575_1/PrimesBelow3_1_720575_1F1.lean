
import IdealArithmetic.Examples.NF3_1_720575_1.RI3_1_720575_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51968533807, 1367117036, -1014518592]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![51968533807, 1367117036, -1014518592]] 
 ![![37, 0, 0], ![23, 1, 0], ![20, 0, 1]] where
  M :=![![![51968533807, 1367117036, -1014518592], ![178555272192, 34059797595, 2734234072], ![-329890234432, 115252859780, 32692680559]]]
  hmulB := by decide  
  f := ![![![-798377786571617031445, 161620889572693932884, -38292315880127236832]], ![![-314141662060670217319, 63593771931097833999, -15067067191825367064]], ![![-1291420434964261342100, 261430770021250276316, -61939948808015655889]]]
  g := ![![![1103113887, 1367117036, -1014518592], ![-17824452809, 34059797595, 2734234072], ![-98231341096, 115252859780, 32692680559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-12, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-12, 1, 0]] 
 ![![37, 0, 0], ![25, 1, 0], ![8, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-12, 1, 0], ![0, -11, 2], ![-176, 19, -12]]]
  hmulB := by decide  
  f := ![![![433, -36, 0], ![1332, 0, 0]], ![![301, -25, 0], ![926, 0, 0]], ![![104, -3, -1], ![320, 19, 0]]]
  g := ![![![1, 0, 0], ![-25, 37, 0], ![-8, 0, 37]], ![![-1, 1, 0], ![7, -11, 2], ![-15, 19, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![51968533807, 1367117036, -1014518592]] ![![37, 0, 0], ![-12, 1, 0]]
  ![![37, 0, 0], ![-27, 6, 1]] where
 M := ![![![1922835750859, 50583330332, -37537187904], ![-445067133492, 17654393163, 14908457176]]]
 hmul := by decide  
 g := ![![![![34314678928, 5290195898, -360672115], ![-24192319649, 0, 0]], ![![-7880268981, -444759231, 249280443], ![5685080785, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-27, 6, 1]] ![![37, 0, 0], ![-12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-444, 37, 0]], ![![-999, 222, 37], ![148, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-12, 1, 0]]], ![![![-27, 6, 1]], ![![4, -2, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![6, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![6, 1, 0]] 
 ![![41, 0, 0], ![6, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![6, 1, 0], ![0, 7, 2], ![-176, 19, 6]]]
  hmulB := by decide  
  f := ![![![31, 5, 0], ![-205, 0, 0]], ![![-6, -1, 0], ![42, 0, 0]], ![![16, -1, -1], ![-106, 21, 0]]]
  g := ![![![1, 0, 0], ![-6, 41, 0], ![-20, 0, 41]], ![![0, 1, 0], ![-2, 7, 2], ![-10, 19, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15629547585223102144594088101, -3163992569470007858725246100, 749634550538883637309763280]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![15629547585223102144594088101, -3163992569470007858725246100, 749634550538883637309763280]] 
 ![![41, 0, 0], ![28, 1, 0], ![4, 0, 1]] where
  M :=![![![15629547585223102144594088101, -3163992569470007858725246100, 749634550538883637309763280], ![-131935680894843520166518337280, 26708611475991883394754344321, -6327985138940015717450492200], ![622830532674143143218902482240, -126083699267351909399038844540, 29872604045461891253479590421]]]
  hmulB := by decide  
  f := ![![![-52744795238859, -180711692883100, -36956991912880]], ![![122623812438508, -146233335004719, -34054125837240]], ![![691269840930164, -22052527999460, -22018429493539]]]
  g := ![![![2468848812883604576577120141, -3163992569470007858725246100, 749634550538883637309763280], ![-20840606382118443715849707548, 26708611475991883394754344321, -6327985138940015717450492200], ![98382529170198757106782238236, -126083699267351909399038844540, 29872604045461891253479590421]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![6, 1, 0]] ![![41, 0, 0], ![6, 1, 0]]
  ![![-52744795238859, -180711692883100, -36956991912880]] where
 M := ![![![1681, 0, 0], ![246, 41, 0]], ![![246, 41, 0], ![36, 13, 2]]]
 hmul := by decide  
 g := ![![![![640811450994147187928357612141, -129723695348270322207735090100, 30735016572094229129700294480]], ![![-38158395383504907298953808674, 7724656059171836242402867721, -1830177835706713893591912520]]], ![![![-38158395383504907298953808674, 7724656059171836242402867721, -1830177835706713893591912520]], ![![2272217726423224426303750036, -459980045066576038545855427, 108981587904960710323274642]]]]
 hle2 := by decide  
def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-52744795238859, -180711692883100, -36956991912880]] ![![15629547585223102144594088101, -3163992569470007858725246100, 749634550538883637309763280]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5635968915631549067561, -439929931253485216538, 48239750226680880926]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-5635968915631549067561, -439929931253485216538, 48239750226680880926]] 
 ![![43, 0, 0], ![0, 43, 0], ![30, 20, 1]] where
  M :=![![![-5635968915631549067561, -439929931253485216538, 48239750226680880926], ![-8490196039895835042976, -5159343592578097546505, -879859862506970433076], ![81672765920561315632176, -12603766713764136635710, -4719413661324612329967]]]
  hmulB := by decide  
  f := ![![![308361120614842662440524322452210647462125, -62423578738851909691435775560840987229342, 14789817094534564862729545734035956973826]], ![![-2603007808638083415840400049190328427393376, 526944066672147485140949915838052842735477, -124847157477703819382871551121681974458684]], ![![-709796948650218851859985460161327236231230, 143688885370236381860894076504294982948258, -34043743983884652254492068814271324418467]]]
  g := ![![![-164724684242604081287, -32668021762490763606, 48239750226680880926], ![416409298495657626728, 289252410640960723605, -879859862506970433076], ![5191980831634876407702, 1901965267737863022410, -4719413661324612329967]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [39, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 42], [0, 1]]
 g := ![![[17, 31], [33, 4], [16], [1, 23], [1]], ![[18, 12], [4, 39], [16], [17, 20], [1]]]
 h' := ![![[25, 42], [3, 17], [37, 2], [4, 4], [4, 25], [0, 1]], ![[0, 1], [41, 26], [1, 41], [18, 39], [27, 18], [25, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [26, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [39, 18, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1281, -596, 125]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-117, -72, 125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-308361120614842662440524322452210647462125, 62423578738851909691435775560840987229342, -14789817094534564862729545734035956973826]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-308361120614842662440524322452210647462125, 62423578738851909691435775560840987229342, -14789817094534564862729545734035956973826]] 
 ![![43, 0, 0], ![3, 1, 0], ![37, 0, 1]] where
  M :=![![![-308361120614842662440524322452210647462125, 62423578738851909691435775560840987229342, -14789817094534564862729545734035956973826], ![2603007808638083415840400049190328427393376, -526944066672147485140949915838052842735477, 124847157477703819382871551121681974458684], ![-12288053762356977813612896523303177966060880, 2487551900357227992057479760251142971054186, -589367645410999394832385691398893829964819]]]
  hmulB := by decide  
  f := ![![![5635968915631549067561, 439929931253485216538, -48239750226680880926]], ![![590653553181174005713, 150677520612524492933, 17096293298300646286]], ![![2950187999018744182967, 671655213259141619712, 68245183789242319435]]]
  g := ![![![1199799434101872288515384721502251136777, 62423578738851909691435775560840987229342, -14789817094534564862729545734035956973826], ![-10128019023732917346581339413901072078407, -526944066672147485140949915838052842735477, 124847157477703819382871551121681974458684], ![47811474808798042302626390179127089057555, 2487551900357227992057479760251142971054186, -589367645410999394832385691398893829964819]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-5635968915631549067561, -439929931253485216538, 48239750226680880926]] ![![-308361120614842662440524322452210647462125, 62423578738851909691435775560840987229342, -14789817094534564862729545734035956973826]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-30, -19, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-30, -19, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![17, 28, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-30, -19, 1], ![-176, -30, -38], ![3432, -449, -11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -28, 47]], ![![-1, -1, 1], ![10, 22, -38], ![77, -3, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [33, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 46], [0, 1]]
 g := ![![[20, 32], [15, 21], [38, 16], [30, 4], [1]], ![[3, 15], [20, 26], [6, 31], [22, 43], [1]]]
 h' := ![![[45, 46], [22, 19], [15, 16], [44, 4], [14, 45], [0, 1]], ![[0, 1], [31, 28], [30, 31], [36, 43], [18, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [36, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [33, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32, -1255, 306]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-110, -209, 306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-9, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-9, 1, 0]] 
 ![![47, 0, 0], ![38, 1, 0], ![11, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-9, 1, 0], ![0, -8, 2], ![-176, 19, -9]]]
  hmulB := by decide  
  f := ![![![208, -23, 0], ![1081, 0, 0]], ![![172, -19, 0], ![894, 0, 0]], ![![64, -3, -1], ![333, 24, 0]]]
  g := ![![![1, 0, 0], ![-38, 47, 0], ![-11, 0, 47]], ![![-1, 1, 0], ![6, -8, 2], ![-17, 19, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-30, -19, 1]] ![![47, 0, 0], ![-9, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-423, 47, 0]], ![![-1410, -893, 47], ![94, 141, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-9, 1, 0]]], ![![![-30, -19, 1]], ![![2, 3, -1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![4, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![4, 1, 0]] 
 ![![53, 0, 0], ![4, 1, 0], ![43, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![4, 1, 0], ![0, 5, 2], ![-176, 19, 4]]]
  hmulB := by decide  
  f := ![![![137, 34, 0], ![-1802, 0, 0]], ![![4, 1, 0], ![-52, 0, 0]], ![![111, 25, -1], ![-1460, 27, 0]]]
  g := ![![![1, 0, 0], ![-4, 53, 0], ![-43, 0, 53]], ![![0, 1, 0], ![-2, 5, 2], ![-8, 19, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1213722319665858303283145, -242714081149406139118826, -20957092056335198601756]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-1213722319665858303283145, -242714081149406139118826, -20957092056335198601756]] 
 ![![53, 0, 0], ![16, 1, 0], ![23, 0, 1]] where
  M :=![![![-1213722319665858303283145, -242714081149406139118826, -20957092056335198601756], ![3688448201914994953909056, -1854621149885633215835335, -485428162298812278237652], ![40873454181337983007958848, -2767343440881219166303166, -1611907068736227076716509]]]
  hmulB := by decide  
  f := ![![![1646130500371719801403997896960605385992992039283, -333237071844502884609098700193075620591870938938, 78952784208621561460239196682552543469957388292]], ![![234762226136417396329469202551706387267459854512, -47524468321151312626530854138739279964898557455, 11259818936772438002747731066692253855388232732]], ![![1952048512519636991169705135323393526931402874081, -395166075996751293624211221059883016796506218964, 93625423342147648730831021842034192674173629199]]]
  g := ![![![59466341434346216801103, -242714081149406139118826, -20957092056335198601756], ![840136496848260543523404, -1854621149885633215835335, -485428162298812278237652], ![2306128524837183253458287, -2767343440881219166303166, -1611907068736227076716509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-21, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-21, 1, 0]] 
 ![![53, 0, 0], ![32, 1, 0], ![2, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-21, 1, 0], ![0, -20, 2], ![-176, 19, -21]]]
  hmulB := by decide  
  f := ![![![22, 799, -80], ![53, 2120, 0]], ![![22, 479, -48], ![54, 1272, 0]], ![![4, 30, -3], ![10, 80, 0]]]
  g := ![![![1, 0, 0], ![-32, 53, 0], ![-2, 0, 53]], ![![-1, 1, 0], ![12, -20, 2], ![-14, 19, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![4, 1, 0]] ![![-1213722319665858303283145, -242714081149406139118826, -20957092056335198601756]]
  ![![53, 0, 0], ![-21, -16, 1]] where
 M := ![![![-64327282942290490074006685, -12863846300918525373297778, -1110725878985765525893068]], ![![-1166441076748438259223524, -2825477474483257772310639, -569256530524153072644676]]]
 hmul := by decide  
 g := ![![![![-1037970002783719456599038, -108807554001109874978554, -29326250003103715110523], ![443565371178731374964651, 0, 0]]], ![![![-14197493406853916457142, -47359788090912418891827, -11112633483551118789338], ![19713044104056223190238, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-21, -16, 1]] ![![53, 0, 0], ![-21, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1113, 53, 0]], ![![-1113, -848, 53], ![265, 318, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-21, 1, 0]]], ![![![-21, -16, 1]], ![![5, 6, -1]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [31, 20, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 41, 19], [41, 17, 40], [0, 1]]
 g := ![![[43, 46, 7], [8, 11, 53], [40, 51], [49, 35, 36], [1]], ![[1, 52, 55, 49], [30, 16, 31, 51], [27, 51], [7, 56, 26, 4], [18, 11, 7, 15]], ![[23, 31, 46, 47], [15, 29, 21, 11], [16, 27], [15, 44, 48, 38], [39, 37, 31, 44]]]
 h' := ![![[24, 41, 19], [47, 56, 19], [47, 17, 17], [15, 17, 13], [28, 39, 6], [0, 1]], ![[41, 17, 40], [11, 42, 30], [9, 0, 22], [16, 46, 13], [50, 55, 17], [24, 41, 19]], ![[0, 1], [48, 20, 10], [1, 42, 20], [5, 55, 33], [39, 24, 36], [41, 17, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 23], []]
 b := ![[], [45, 17, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [31, 20, 53, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-75697, 15576, -8614]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1283, 264, -146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![13, 12, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![13, 12, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![13, 12, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![13, 12, 1], ![-176, 44, 24], ![-2024, 140, 32]]]
  hmulB := by decide  
  f := ![![![-12, -12, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -12, 61]], ![![0, 0, 1], ![-8, -4, 24], ![-40, -4, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [55, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 60], [0, 1]]
 g := ![![[3, 3], [22], [35, 22], [58, 15], [18, 1]], ![[57, 58], [22], [4, 39], [23, 46], [36, 60]]]
 h' := ![![[18, 60], [7, 53], [27, 49], [43, 49], [47, 25], [0, 1]], ![[0, 1], [46, 8], [55, 12], [10, 12], [9, 36], [18, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [60, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [55, 43, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1221, -1906, 258]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75, -82, 258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-24, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-24, 1, 0]] 
 ![![61, 0, 0], ![37, 1, 0], ![29, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-24, 1, 0], ![0, -23, 2], ![-176, 19, -24]]]
  hmulB := by decide  
  f := ![![![769, -32, 0], ![1952, 0, 0]], ![![457, -19, 0], ![1160, 0, 0]], ![![353, -3, -1], ![896, 31, 0]]]
  g := ![![![1, 0, 0], ![-37, 61, 0], ![-29, 0, 61]], ![![-1, 1, 0], ![13, -23, 2], ![-3, 19, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![13, 12, 1]] ![![61, 0, 0], ![-24, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1464, 61, 0]], ![![793, 732, 61], ![-488, -244, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-24, 1, 0]]], ![![![13, 12, 1]], ![![-8, -4, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [27, 26, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 52, 22], [63, 14, 45], [0, 1]]
 g := ![![[24, 27, 6], [33, 56, 40], [66, 21], [34, 29], [18, 1], []], ![[64, 53, 30, 33], [3, 58, 45, 33], [47, 60], [61, 56], [13, 62], [12, 15]], ![[4, 4, 11, 34], [11, 4, 38, 18], [45, 36], [31, 10], [59, 24], [56, 15]]]
 h' := ![![[22, 52, 22], [47, 59, 26], [33, 42, 24], [41, 21, 50], [50, 41, 30], [0, 0, 1], [0, 1]], ![[63, 14, 45], [11, 29, 54], [40, 23, 54], [61, 46, 23], [57, 17, 49], [26, 30, 14], [22, 52, 22]], ![[0, 1], [43, 46, 54], [7, 2, 56], [63, 0, 61], [30, 9, 55], [45, 37, 52], [63, 14, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 48], []]
 b := ![[], [37, 9, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [27, 26, 49, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-344581, 48642, 4690]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5143, 726, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [65, 32, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 14, 36], [67, 56, 35], [0, 1]]
 g := ![![[31, 23, 43], [23, 22, 57], [54, 55, 10], [68, 36], [40, 1], []], ![[16, 70, 17, 37], [12, 58, 41, 45], [67, 57, 53, 45], [36, 5], [5, 12], [24, 18]], ![[32, 6, 54, 70], [35, 66, 9, 68], [49, 65, 46, 62], [10, 50], [60, 54], [25, 18]]]
 h' := ![![[44, 14, 36], [67, 2, 55], [40, 23, 25], [1, 31, 62], [27, 4, 6], [0, 0, 1], [0, 1]], ![[67, 56, 35], [32, 35, 28], [15, 67, 27], [40, 43, 44], [45, 9, 54], [21, 4, 56], [44, 14, 36]], ![[0, 1], [30, 34, 59], [51, 52, 19], [16, 68, 36], [13, 58, 11], [24, 67, 14], [67, 56, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 48], []]
 b := ![[], [11, 69, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [65, 32, 31, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![63913561, -25822416, 788952]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![900191, -363696, 11112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [68, 43, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 11, 14], [40, 61, 59], [0, 1]]
 g := ![![[14, 57, 32], [48, 69], [39, 3], [19, 41, 71], [37, 1], []], ![[3, 50, 38, 33], [1, 38], [13, 37], [44, 26, 6, 13], [8, 71], [41, 50]], ![[50, 70, 3, 45], [40, 27], [16, 55], [67, 3, 22, 17], [14, 48], [69, 50]]]
 h' := ![![[70, 11, 14], [67, 64, 18], [22, 9, 19], [22, 33, 52], [39, 20, 12], [0, 0, 1], [0, 1]], ![[40, 61, 59], [4, 22, 23], [46, 28, 44], [28, 15, 57], [65, 33, 63], [68, 27, 61], [70, 11, 14]], ![[0, 1], [42, 60, 32], [34, 36, 10], [63, 25, 37], [16, 20, 71], [47, 46, 11], [40, 61, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 59], []]
 b := ![[], [45, 56, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [68, 43, 36, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25988, -3066, 730]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-356, -42, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-46, -29, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-46, -29, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![33, 50, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-46, -29, 1], ![-176, -56, -58], ![5192, -639, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -50, 79]], ![![-1, -1, 1], ![22, 36, -58], ![77, 9, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [35, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 78], [0, 1]]
 g := ![![[15, 44], [37, 36], [42, 45], [40, 25], [73], [1]], ![[62, 35], [18, 43], [38, 34], [29, 54], [73], [1]]]
 h' := ![![[28, 78], [48, 26], [31, 6], [22, 19], [13, 5], [44, 28], [0, 1]], ![[0, 1], [65, 53], [41, 73], [1, 60], [74, 74], [38, 51], [28, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [55, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [35, 51, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3045, -1468, 748]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-351, -492, 748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-21, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-21, 1, 0]] 
 ![![79, 0, 0], ![58, 1, 0], ![27, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-21, 1, 0], ![0, -20, 2], ![-176, 19, -21]]]
  hmulB := by decide  
  f := ![![![22, 1199, -120], ![79, 4740, 0]], ![![22, 879, -88], ![80, 3476, 0]], ![![3, 410, -41], ![10, 1620, 0]]]
  g := ![![![1, 0, 0], ![-58, 79, 0], ![-27, 0, 79]], ![![-1, 1, 0], ![14, -20, 2], ![-9, 19, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-46, -29, 1]] ![![79, 0, 0], ![-21, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1659, 79, 0]], ![![-3634, -2291, 79], ![790, 553, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-21, 1, 0]]], ![![![-46, -29, 1]], ![![10, 7, -1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB241I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB241I1 : PrimesBelowBoundCertificateInterval O 31 79 241 where
  m := 11
  g := ![3, 3, 2, 2, 3, 1, 2, 1, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB241I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N1]
    · exact ![I41N0, I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
    · exact ![389017]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I41N0, I41N1, I43N1, I47N1, I53N0, I53N1, I53N2, I61N1, I79N1]
  Il := ![[I37N0, I37N1, I37N1], [I41N0, I41N0, I41N1], [I43N1], [I47N1], [I53N0, I53N1, I53N2], [], [I61N1], [], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
