
import IdealArithmetic.Examples.NF3_1_797667_1.RI3_1_797667_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [25, 5, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 23, 2], [20, 13, 35], [0, 1]]
 g := ![![[30, 10, 25], [16, 36], [7, 2, 34], [10, 1], []], ![[5, 12, 21, 23], [34, 16], [22, 14, 28, 29], [14, 21], [21, 4]], ![[15, 11, 18, 31], [13, 4], [5, 25, 25, 5], [27, 11], [25, 4]]]
 h' := ![![[27, 23, 2], [33, 13, 5], [10, 33, 6], [9, 36, 21], [0, 0, 1], [0, 1]], ![[20, 13, 35], [35, 8, 17], [16, 25, 33], [11, 35, 12], [19, 1, 13], [27, 23, 2]], ![[0, 1], [19, 16, 15], [23, 16, 35], [0, 3, 4], [34, 36, 23], [20, 13, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 6], []]
 b := ![[], [23, 31, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [25, 5, 27, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-581159, 133126, -11396]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15707, 3598, -308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-303078005608355, 4892525866344, 10725763284582]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-303078005608355, 4892525866344, 10725763284582]] 
 ![![41, 0, 0], ![0, 41, 0], ![39, 4, 1]] where
  M :=![![![-303078005608355, 4892525866344, 10725763284582], ![-2059346550639744, -82729502498477, 36129104168196], ![-2998711516977792, -433545121035876, -46600398330281]]]
  hmulB := by decide  
  f := ![![![476068892917397861497553213, -107856309443985965059651248, 25953649685869151204004318]], ![![-4983100739686877031168829056, 1128951845764636001841295139, -271661628960219592770945108]], ![![350234013136327725219840723, -79347650435952962351563664, 19093561919815486218115561]]]
  g := ![![![-17594701797733, -927086031024, 10725763284582], ![-84594673492668, -5542583394421, 36129104168196], ![-28812097124313, -6027890919872, -46600398330281]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [11, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 40], [0, 1]]
 g := ![![[2, 37], [36], [4], [4, 33], [1]], ![[8, 4], [36], [4], [16, 8], [1]]]
 h' := ![![[19, 40], [9, 18], [6, 6], [38, 39], [30, 19], [0, 1]], ![[0, 1], [23, 23], [38, 35], [0, 2], [22, 22], [19, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [2, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [11, 22, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1354, -3401, 1210]
  a := ![-1, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1184, -201, 1210]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-476068892917397861497553213, 107856309443985965059651248, -25953649685869151204004318]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-476068892917397861497553213, 107856309443985965059651248, -25953649685869151204004318]] 
 ![![41, 0, 0], ![27, 1, 0], ![12, 0, 1]] where
  M :=![![![-476068892917397861497553213, 107856309443985965059651248, -25953649685869151204004318], ![4983100739686877031168829056, -1128951845764636001841295139, 271661628960219592770945108], ![-15725310673558428260284210560, 3562664982617162826452892108, -857290216804416409070350031]]]
  hmulB := by decide  
  f := ![![![303078005608355, -4892525866344, -10725763284582]], ![![249815919562569, -1204114533971, -7944505191510]], ![![161845063031172, 9142312454628, -2002652709383]]]
  g := ![![![-75042571992063148869758173, 107856309443985965059651248, -25953649685869151204004318], ![785484415312424730917864793, -1128951845764636001841295139, 271661628960219592770945108], ![-2478775185428507991845563344, 3562664982617162826452892108, -857290216804416409070350031]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-303078005608355, 4892525866344, 10725763284582]] ![![-476068892917397861497553213, 107856309443985965059651248, -25953649685869151204004318]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44217312866008179577994441028512179, -10017701744871626647651860309250127, 2410576841394192856769575379862152]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![44217312866008179577994441028512179, -10017701744871626647651860309250127, 2410576841394192856769575379862152]] 
 ![![43, 0, 0], ![0, 43, 0], ![16, 24, 1]] where
  M :=![![![44217312866008179577994441028512179, -10017701744871626647651860309250127, 2410576841394192856769575379862152], ![-462830753547685028499758472933533184, 104857128280157856217807384314867498, -25231951551826494229416430168026077], ![1460567981467667287849398706442491200, -330900578712013802439167835487360267, 79625176728331361988390954146841421]]]
  hmulB := by decide  
  f := ![![![451823069955426793, -8735632993693119, -16446698784501719]], ![![3157766166624330048, 115178028474583813, -59100296550082795]], ![![2043036391155445552, 75892772136010513, -37801780600686362]]]
  g := ![![![131350776830257996969331045365529, -1578408045077494307212131847114925, 2410576841394192856769575379862152], ![-1374872760894444670444083494072464, 16521487570325435295902365310406822, -25231951551826494229416430168026077], ![4338724507310825489189382327744848, -52137321399813174189780249651431497, 79625176728331361988390954146841421]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [41, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 42], [0, 1]]
 g := ![![[7, 21], [13, 40], [6], [5, 24], [1]], ![[0, 22], [14, 3], [6], [40, 19], [1]]]
 h' := ![![[14, 42], [26, 35], [26, 30], [10, 36], [2, 14], [0, 1]], ![[0, 1], [0, 8], [16, 13], [41, 7], [26, 29], [14, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [30, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [41, 29, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2281, -384, 285]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53, -168, 285]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-451823069955426793, 8735632993693119, 16446698784501719]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-451823069955426793, 8735632993693119, 16446698784501719]] 
 ![![43, 0, 0], ![12, 1, 0], ![42, 0, 1]] where
  M :=![![![-451823069955426793, 8735632993693119, 16446698784501719], ![-3157766166624330048, -115178028474583813, 59100296550082795], ![-4835007701413408896, -638886646357530451, -56077731924501018]]]
  hmulB := by decide  
  f := ![![![-44217312866008179577994441028512179, 10017701744871626647651860309250127, -2410576841394192856769575379862152]], ![![-1576209321963095963631972544386348, 357099829262829384977091613863582, -85929547555902791902755218379529]], ![![-77155700507907228607561982084651226, 17480094232479584224198743452927107, -4206265210857847952853793490722135]]]
  g := ![![![-29009581740205033, 8735632993693119, 16446698784501719], ![-99019587907739574, -115178028474583813, 59100296550082795], ![120625506876883704, -638886646357530451, -56077731924501018]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![44217312866008179577994441028512179, -10017701744871626647651860309250127, 2410576841394192856769575379862152]] ![![-451823069955426793, 8735632993693119, 16446698784501719]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [39, 7, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 34, 29], [26, 12, 18], [0, 1]]
 g := ![![[24, 21, 36], [7, 6, 24], [8, 6, 8], [0, 30, 1], []], ![[26, 34, 29, 23], [22, 27, 1, 22], [25, 41, 22, 19], [4, 29, 25, 40], [36, 42]], ![[4, 42, 24, 25], [16, 1, 14, 17], [21, 24, 27, 14], [1, 32, 33, 34], [0, 42]]]
 h' := ![![[4, 34, 29], [9, 6, 41], [17, 39, 27], [0, 5, 33], [0, 0, 1], [0, 1]], ![[26, 12, 18], [42, 42, 8], [15, 34, 45], [41, 27, 24], [22, 27, 12], [4, 34, 29]], ![[0, 1], [10, 46, 45], [13, 21, 22], [19, 15, 37], [18, 20, 34], [26, 12, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 20], []]
 b := ![[], [7, 16, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [39, 7, 17, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5191808, 1277272, -167931]
  a := ![1, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-110464, 27176, -3573]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [50, 9, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 21, 21], [24, 31, 32], [0, 1]]
 g := ![![[22, 20, 43], [3, 7], [30, 27, 28], [8, 44], [1]], ![[0, 45, 4, 33], [36, 42], [12, 36, 32, 14], [37, 16], [34, 8, 23, 39]], ![[31, 21, 5, 48], [42, 36], [20, 3, 46, 23], [1, 38], [49, 39, 32, 14]]]
 h' := ![![[13, 21, 21], [0, 26, 34], [37, 52, 22], [33, 6, 44], [3, 44, 37], [0, 1]], ![[24, 31, 32], [40, 21, 10], [12, 29, 25], [34, 14, 6], [20, 30, 4], [13, 21, 21]], ![[0, 1], [4, 6, 9], [14, 25, 6], [20, 33, 3], [32, 32, 12], [24, 31, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 27], []]
 b := ![[], [48, 21, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [50, 9, 16, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-564238, 143789, -15317]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10646, 2713, -289]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-362739587232030179757443275, 82180864471793796905664941, -19775323097723105431305230]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-362739587232030179757443275, 82180864471793796905664941, -19775323097723105431305230]] 
 ![![59, 0, 0], ![0, 59, 0], ![28, 42, 1]] where
  M :=![![![-362739587232030179757443275, 82180864471793796905664941, -19775323097723105431305230], ![3796862034762836242810604160, -860202236756009190720518046, 206991947219935179854384363], ![-11981863943821572763077064512, 2714564308793825006584225261, -653210289536074010866133683]]]
  hmulB := by decide  
  f := ![![![18553315560175, 2969604323853, 379336295983]], ![![-72832568828736, 23549773451965, 9667485563525]], ![![-53940197527636, 18909055628003, 7624967270696]]]
  g := ![![![3236770500071470717272935, 15470244653833291949499739, -19775323097723105431305230], ![-33879872667717776154443356, -161929898643954012620417988, 206991947219935179854384363], ![106915663782855924426689468, 511006719818795482423082033, -653210289536074010866133683]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [1, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 58], [0, 1]]
 g := ![![[44, 1], [44, 1], [9], [42, 26], [15, 1]], ![[0, 58], [0, 58], [9], [19, 33], [30, 58]]]
 h' := ![![[15, 58], [15, 58], [44, 1], [17, 3], [44, 47], [0, 1]], ![[0, 1], [0, 1], [0, 58], [3, 56], [41, 12], [15, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [58, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [1, 44, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-84434, -25171, 12059]
  a := ![1, -1, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7154, -9011, 12059]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18553315560175, -2969604323853, -379336295983]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-18553315560175, -2969604323853, -379336295983]] 
 ![![59, 0, 0], ![49, 1, 0], ![42, 0, 1]] where
  M :=![![![-18553315560175, -2969604323853, -379336295983], ![72832568828736, -23549773451965, -9667485563525], ![642996599008512, -43394876001763, -33217259015490]]]
  hmulB := by decide  
  f := ![![![362739587232030179757443275, -82180864471793796905664941, 19775323097723105431305230]], ![![236904707450960043479730785, -53672205463760794197577357, 12915235331669440445416473]], ![![461303840806217632421859018, -104511196891680753841053437, 25148709485431261677643277]]]
  g := ![![![2421854588812, -2969604323853, -379336295983], ![27674675621069, -23549773451965, -9667485563525], ![70584244097381, -43394876001763, -33217259015490]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-362739587232030179757443275, 82180864471793796905664941, -19775323097723105431305230]] ![![-18553315560175, -2969604323853, -379336295983]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14142899, 972737, -119918]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![14142899, 972737, -119918]] 
 ![![61, 0, 0], ![0, 61, 0], ![29, 42, 1]] where
  M :=![![![14142899, 972737, -119918], ![23024256, 10651884, 2678375], ![-163741248, 26423377, 13330259]]]
  hmulB := by decide  
  f := ![![![-1167551806321, 264515978229, -63650935867]], ![![12220979686464, -2768737437757, 666246062953]], ![![7227148464175, -1637354535754, 393999444739]]]
  g := ![![![288861, 98513, -119918], ![-895879, -1669506, 2678375], ![-9021619, -8745041, 13330259]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [32, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 60], [0, 1]]
 g := ![![[25, 14], [5], [8, 3], [42, 45], [54, 1]], ![[49, 47], [5], [48, 58], [32, 16], [47, 60]]]
 h' := ![![[54, 60], [45, 40], [49, 35], [59, 8], [41, 17], [0, 1]], ![[0, 1], [9, 21], [48, 26], [3, 53], [44, 44], [54, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [58, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [32, 7, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26, 4, 3]
  a := ![-1, 1, 0]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -2, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1167551806321, 264515978229, -63650935867]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-1167551806321, 264515978229, -63650935867]] 
 ![![61, 0, 0], ![55, 1, 0], ![47, 0, 1]] where
  M :=![![![-1167551806321, 264515978229, -63650935867], ![12220979686464, -2768737437757, 666246062953], ![-38566088133504, 8737382336159, -2102491374804]]]
  hmulB := by decide  
  f := ![![![14142899, 972737, -119918]], ![![13129241, 1051679, -64215]], ![![8212705, 1182656, 126133]]]
  g := ![![![-208595682347, 264515978229, -63650935867], ![2183409406628, -2768737437757, 666246062953], ![-6890246262401, 8737382336159, -2102491374804]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![14142899, 972737, -119918]] ![![-1167551806321, 264515978229, -63650935867]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [13, 9, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 15, 17], [55, 51, 50], [0, 1]]
 g := ![![[58, 19, 35], [3, 20, 33], [20, 17], [63, 47], [38, 1], []], ![[41, 1, 30, 24], [44, 18, 45, 15], [3, 9], [14, 55], [41, 55], [35, 21]], ![[45, 59, 24, 57], [47, 56, 39, 8], [43, 29], [37, 60], [17, 24], [2, 21]]]
 h' := ![![[50, 15, 17], [28, 14, 13], [57, 55, 57], [7, 23, 33], [42, 47, 28], [0, 0, 1], [0, 1]], ![[55, 51, 50], [44, 6, 30], [45, 13, 23], [34, 23, 64], [22, 44, 16], [35, 41, 51], [50, 15, 17]], ![[0, 1], [54, 47, 24], [26, 66, 54], [7, 21, 37], [35, 43, 23], [51, 26, 15], [55, 51, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 54], []]
 b := ![[], [10, 38, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [13, 9, 29, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2931853, -957966, 148941]
  a := ![0, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43759, -14298, 2223]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-139186338252468899801125446503, -5201222605422129672733090107, 2565549933239881037520332932]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-139186338252468899801125446503, -5201222605422129672733090107, 2565549933239881037520332932]] 
 ![![71, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-139186338252468899801125446503, -5201222605422129672733090107, 2565549933239881037520332932], ![-492585587182057159203903922944, -80108567049009268340465364824, -10472567949786626943158604457], ![506049153058991737960849377600, -237503171375858775003411538847, -90581134998795895283623969281]]]
  hmulB := by decide  
  f := ![![![-4769056825902901815252085627646667665073789347099271130465, 1080458892448125348394706430458648914016396877169864412471, -259992686001777752950020497458463341660673932374674390867]], ![![635908998400541221847209153301102731461628248856876224169, -144069059604792037002852339074287293520393548267146948432, 34667586187873842061043067591557136860100969498388310772]], ![![-2218725516023925891906756325859656759046462047896851889408, 502665789316894647377321970599363299681380718863392566271, -120957335479542808962156960679915868946992901934888074584]]]
  g := ![![![-1887114304887982677864681076, -5201222605422129672733090107, 2565549933239881037520332932], ![-5809535494831660434696317720, -80108567049009268340465364824, -10472567949786626943158604457], ![10472567949786626943158604457, -237503171375858775003411538847, -90581134998795895283623969281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-249652474690296950307840592337, -3844351348718332953421786395, 6339778543015846393249695084]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-249652474690296950307840592337, -3844351348718332953421786395, 6339778543015846393249695084]] 
 ![![71, 0, 0], ![7, 1, 0], ![57, 0, 1]] where
  M :=![![![-249652474690296950307840592337, -3844351348718332953421786395, 6339778543015846393249695084], ![-1217237480259042507503941456128, -112672773938245843096175209178, 1146503039876693926234030983], ![-479122021305122580446958468288, -397720305473877311684342268495, -111526270898369149169941178195]]]
  hmulB := by decide  
  f := ![![![-13021961848354000930148853199172597571936482936034232254295, 2950204828710666865166464406103099274501519604499531235605, -709912874088106423240592824367637900715265553234780404667]], ![![635908998400541221847209153301102731461628248856876224169, -144069059604792037002852339074287293520393548267146948432, 34667586187873842061043067591557136860100969498388310772]], ![![-16512505361179009265750027831634459793906201481644836592041, 3741008737237145586549491054851037161223687419897217698740, -900205381943396916324835920230668043382460394166445100795]]]
  g := ![![![-8226892847903829071114376160, -3844351348718332953421786395, 6339778543015846393249695084], ![-6956038534708354360930348703, -112672773938245843096175209178, 1146503039876693926234030983], ![121998838848155776113099782652, -397720305473877311684342268495, -111526270898369149169941178195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8198098244862619730449, -774306418103029443228, 2824279379165841278]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-8198098244862619730449, -774306418103029443228, 2824279379165841278]] 
 ![![71, 0, 0], ![62, 1, 0], ![41, 0, 1]] where
  M :=![![![-8198098244862619730449, -774306418103029443228, 2824279379165841278], ![-542261640799841525376, -7364481959797107620383, -2317270695550756647128], ![148124570634981811574400, -16401648749121910371688, -9681752655347864267511]]]
  hmulB := by decide  
  f := ![![![33294032764470163128339938285812957410564649, -7542966057868365136688043340554168572302772, 1815076926584315839374638585602342760818658]], ![![24165285373140302433762613595559909146166562, -5474792694468020811024835143525945458066375, 1317408804616776314224123090942076492612476]], ![![34715634599293157089381847643226504361100007, -7865038618550062400611135442175712528502884, 1892577802114502064435784803989500802230327]]]
  g := ![![![559057805957456426159, -774306418103029443228, 2824279379165841278], ![7761460822312702161558, -7364481959797107620383, -2317270695550756647128], ![21999699323236657599817, -16401648749121910371688, -9681752655347864267511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-139186338252468899801125446503, -5201222605422129672733090107, 2565549933239881037520332932]] ![![-249652474690296950307840592337, -3844351348718332953421786395, 6339778543015846393249695084]]
  ![![39850125416526893372077482018331691611948123750795212512791, 100746062850615557297022276594431646691692557012778551391, -1174499995119943757035815159027288424561456646527211694173]] where
 M := ![![![39850125416526893372077482018331691611948123750795212512791, 100746062850615557297022276594431646691692557012778551391, -1174499995119943757035815159027288424561456646527211694173]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![39850125416526893372077482018331691611948123750795212512791, 100746062850615557297022276594431646691692557012778551391, -1174499995119943757035815159027288424561456646527211694173]] ![![-8198098244862619730449, -774306418103029443228, 2824279379165841278]]
  ![![71, 0, 0]] where
 M := ![![![-500722181448059798359762817845839407495990285139731322575706991011476201867242375, -12334414058808661521522991237755024885564976257379484491180328033450126829158077, 11250310434793792422681043050221006652036494802022746094123527458673655842145253]]]
 hmul := by decide  
 g := ![![![![-7052425090817743638869898842899146584450567396334243979939535084668678899538625, -173724141673361429880605510390915843458661637427880063256060958217607420128987, 158455076546391442572972437327056431718823870451024592874979259981319096368243]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2259478015477774538091643, -511898516464376664496534, 123179022530270313171372]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![2259478015477774538091643, -511898516464376664496534, 123179022530270313171372]] 
 ![![73, 0, 0], ![24, 1, 0], ![35, 0, 1]] where
  M :=![![![2259478015477774538091643, -511898516464376664496534, 123179022530270313171372], ![-23650372325811900128903424, 5358136005077827779186989, -1289337504332589367146858], ![74634142835348419454431104, -16908819972265425612995814, 4068798500745238412040131]]]
  hmulB := by decide  
  f := ![![![13444943803147, 1966817769146, 216220311264]], ![![3851566459080, 866059986713, 157838101374]], ![![704516735225, 1360695609712, 409854210887]]]
  g := ![![![140188720850182925000143, -511898516464376664496534, 123179022530270313171372], ![-1467381147890947109304810, 5358136005077827779186989, -1289337504332589367146858], ![4630655817036099859519535, -16908819972265425612995814, 4068798500745238412040131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2743872530215465058645395310819, 142296975892681767208750321367, -37976495621435687967523172267]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![2743872530215465058645395310819, 142296975892681767208750321367, -37976495621435687967523172267]] 
 ![![73, 0, 0], ![49, 1, 0], ![19, 0, 1]] where
  M :=![![![2743872530215465058645395310819, 142296975892681767208750321367, -37976495621435687967523172267], ![7291487159315652089764449075264, 1804069146272633844118658371845, 350937936435173925691204619567], ![-20029532212079247214315612627200, 4887061274818101509759915362057, 2155007082707807769809862991412]]]
  hmulB := by decide  
  f := ![![![-2172726588895239036544924525131645633143940036449741386025821, 492244452001448928815336850932182062823519345761309447573423, -118449631114933329375195764094601815141040438035477904010704]], ![![-1146866762764376897954297466099823116670867091551035210208357, 259829655530968625064549770871595277594837525497918850866763, -62523257956948671392999635836002005256472661678430750161995]], ![![-1548635764372884065573433625346803761435216588711023872582639, 350852871723351008511962496465991414657435557975702371280440, -84426331393418370036609218016993941690693147156399924100391]]]
  g := ![![![-48042820160529636482197673467, 142296975892681767208750321367, -37976495621435687967523172267], ![-1202407147949475491235379437218, 1804069146272633844118658371845, 350937936435173925691204619567], ![-4115625606159103682451217290477, 4887061274818101509759915362057, 2155007082707807769809862991412]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-185919039306117869084062624842723847, 42121091575728160016232614304195685, -10135670882662666427255120614270190]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-185919039306117869084062624842723847, 42121091575728160016232614304195685, -10135670882662666427255120614270190]] 
 ![![73, 0, 0], ![72, 1, 0], ![48, 0, 1]] where
  M :=![![![-185919039306117869084062624842723847, 42121091575728160016232614304195685, -10135670882662666427255120614270190], ![1946048809471231954032983157939876480, -440889219417762024072652772046593522, 106091932961859147194187601684046675], ![-6141200773068574769083678788465695040, 1391326467223424681703640931101618885, -334797286455902876878465170362546847]]]
  hmulB := by decide  
  f := ![![![8152480411909732241, 73164847328782955, -223623850261888195]], ![![8628963957640866504, 118507996119913287, -223680416128676405]], ![![5756262853901689776, 222322835325759365, -103814839205846078]]]
  g := ![![![-37426375758777224681432398154244439, 42121091575728160016232614304195685, -10135670882662666427255120614270190], ![391748764731244638656753121430963968, -440889219417762024072652772046593522, 106091932961859147194187601684046675], ![-1236252557031120736459993118498356248, 1391326467223424681703640931101618885, -334797286455902876878465170362546847]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![2259478015477774538091643, -511898516464376664496534, 123179022530270313171372]] ![![2743872530215465058645395310819, 142296975892681767208750321367, -37976495621435687967523172267]]
  ![![8152480411909732241, 73164847328782955, -223623850261888195]] where
 M := ![![![8152480411909732241, 73164847328782955, -223623850261888195]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![8152480411909732241, 73164847328782955, -223623850261888195]] ![![-185919039306117869084062624842723847, 42121091575728160016232614304195685, -10135670882662666427255120614270190]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6512965181563824815886488439701, -178931093280375185614632632123, 140473438406057602176625048339]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-6512965181563824815886488439701, -178931093280375185614632632123, 140473438406057602176625048339]] 
 ![![79, 0, 0], ![0, 79, 0], ![28, 61, 1]] where
  M :=![![![-6512965181563824815886488439701, -178931093280375185614632632123, 140473438406057602176625048339], ![-26970900173963059617912009281088, -3384091881756239984562729792459, -255846403029010352490647799691], ![7383869735868976020097456086528, -10781224879190759006738537691533, -3639938284785250337053377592150]]]
  hmulB := by decide  
  f := ![![![121006936633514759363670407068000600197794146652329034390893, -27414859060488321313762690811008492366155705234528254160103, 6596884798964013410803507577402195371904885321383596313286]], ![![-1266601881401090574874273454861221511405737981705650492150912, 286956376472247362304306757004455195373952443635912811130002, -69050807583536937119681057278221086354657345060817569853737]], ![![-884524930145765122630123369212380840092602827271591047489516, 200394514315126084628457784160281531940180066319362243157225, -48221277459950004602701526355417603648119824824506782569996]]]
  g := ![![![-132230651353587818694075820167, -110731782734808720485933678238, 140473438406057602176625048339], ![-250724061887984427192074315060, 154715679784979639460339063148, -255846403029010352490647799691], ![1383571414048809942501164919832, 2674114056869740652576170828223, -3639938284785250337053377592150]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [39, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 78], [0, 1]]
 g := ![![[38, 67], [23, 64], [78, 8], [31, 25], [45], [1]], ![[47, 12], [54, 15], [72, 71], [32, 54], [45], [1]]]
 h' := ![![[19, 78], [51, 15], [39, 8], [55, 18], [3, 5], [40, 19], [0, 1]], ![[0, 1], [20, 64], [33, 71], [2, 61], [19, 74], [6, 60], [19, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [71, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [39, 60, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5981, -596, 156]
  a := ![2, -2, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-131, -128, 156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69792475252793230791842437661284398244110654989971, 3531484286067401288291708491655366655152145095892, -993829934040383451767514108732385566315358044936]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![69792475252793230791842437661284398244110654989971, 3531484286067401288291708491655366655152145095892, -993829934040383451767514108732385566315358044936]] 
 ![![79, 0, 0], ![52, 1, 0], ![64, 0, 1]] where
  M :=![![![69792475252793230791842437661284398244110654989971, 3531484286067401288291708491655366655152145095892, -993829934040383451767514108732385566315358044936], ![190815347335753622739362708876618028732548744627712, 45390562351877777016432932886248934696335990950423, 8606792990121436961340097257501328832825719197804], ![-487229635589187424612645321521212369056663113783552, 123852666709434599642501583761381978073962949260532, 53997355341999213977773030143750263529161710148227]]]
  hmulB := by decide  
  f := ![![![1384996060844907517952865716011572825818002244644801340251012100845020033285993585651906395900078293, -313779299466030854833615148904999528775029675268782857579368695694852667604094046665175644876049436, 75505253786271520290052030275583575256781596254511931230788844040452344684515466053409340678029096]], ![![728136537176848848580494017970756208775114560008397201224571787192078374068920214830943533881297276, -164963770663429925980638154966533519763494907249599668866458552591683123748708582368993105551137113, 39695516532412272546353977065398917437229331290345515363601158115188210255082949707450347620068644]], ![![1701118540058074346599335754450487644656402213012750678923950708502862583934970594420014427134492608, -385398773973749350321011255325368844414134205197115689313744067545380936462959079357093630991970340, 92739171409094532576204582938953731843138503395566754964188660012337578299122165050229971457424187]]]
  g := ![![![-635944200558570826407664568935721412400227533171, 3531484286067401288291708491655366655152145095892, -993829934040383451767514108732385566315358044936], ![-34434539826957756299252101590992552161743909031060, 45390562351877777016432932886248934696335990950423, 8606792990121436961340097257501328832825719197804], ![-131435430966680206336711412738140406262899821833136, 123852666709434599642501583761381978073962949260532, 53997355341999213977773030143750263529161710148227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-6512965181563824815886488439701, -178931093280375185614632632123, 140473438406057602176625048339]] ![![69792475252793230791842437661284398244110654989971, 3531484286067401288291708491655366655152145095892, -993829934040383451767514108732385566315358044936]]
  ![![79, 0, 0]] where
 M := ![![![-557141582174601747470722008589032580171594824310405274415223271688825633063551375, -13724207192195552960567835320882351633234269356802524997228815699190986190189973, 12517951047164923963264822548837458105787085765630942837123361538524208613091197]]]
 hmul := by decide  
 g := ![![![![-7052425090817743638869898842899146584450567396334243979939535084668678899538625, -173724141673361429880605510390915843458661637427880063256060958217607420128987, 158455076546391442572972437327056431718823870451024592874979259981319096368243]]]]
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


lemma PB253I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB253I1 : PrimesBelowBoundCertificateInterval O 31 79 253 where
  m := 11
  g := ![1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB253I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
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
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I41N1, I43N1, I59N1, I61N1, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2, I79N1]
  Il := ![[], [I41N1], [I43N1], [], [], [I59N1], [I61N1], [], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
