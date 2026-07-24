
import IdealArithmetic.Examples.NF3_1_439803_1.RI3_1_439803_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 8, -4]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-21, 8, -4]] 
 ![![37, 0, 0], ![20, 1, 0], ![36, 0, 1]] where
  M :=![![![-21, 8, -4], ![-292, 55, 60], ![560, -196, 71]]]
  hmulB := by decide  
  f := ![![![-15665, -216, -700]], ![![-9936, -137, -444]], ![![-15956, -220, -713]]]
  g := ![![![-1, 8, -4], ![-96, 55, 60], ![52, -196, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40358, -4290, -15101]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![40358, -4290, -15101]] 
 ![![37, 0, 0], ![23, 1, 0], ![11, 0, 1]] where
  M :=![![![40358, -4290, -15101], ![-1171357, 361769, -49421], ![-541744, -15617, 353189]]]
  hmulB := by decide  
  f := ![![![127001023584, 1751013127, 5675089759]], ![![90851553517, 1252606147, 4059736736]], ![![43548392617, 600418839, 1945976733]]]
  g := ![![![8247, -4290, -15101], ![-241849, 361769, -49421], ![-109936, -15617, 353189]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60394893301876, 832688178339, 2698769118555]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![60394893301876, 832688178339, 2698769118555]] 
 ![![37, 0, 0], ![31, 1, 0], ![32, 0, 1]] where
  M :=![![![60394893301876, 832688178339, 2698769118555], ![209470598485413, 2888053633882, 9360274545267], ![101899757391873, 1404932084766, 4553429990560]]]
  hmulB := by decide  
  f := ![![![8051398, -3046710, 1491003]], ![![9683977, -3098945, 630768]], ![![1187084, -623697, 578533]]]
  g := ![![![-1399433838389, 832688178339, 2698769118555], ![-4853725665229, 2888053633882, 9360274545267], ![-2361159376589, 1404932084766, 4553429990560]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-21, 8, -4]] ![![40358, -4290, -15101]]
  ![![-8051398, 3046710, -1491003]] where
 M := ![![![-8051398, 3046710, -1491003]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-8051398, 3046710, -1491003]] ![![60394893301876, 832688178339, 2698769118555]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [38, 15, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 31, 25], [22, 9, 16], [0, 1]]
 g := ![![[21, 25, 16], [7, 20], [27, 33], [35, 3, 1], []], ![[26, 40], [31, 4], [7, 23], [10, 33, 19, 16], [22, 10]], ![[8, 12, 2, 10], [35, 2], [23, 39], [20, 37, 17, 1], [31, 10]]]
 h' := ![![[22, 31, 25], [5, 33, 4], [36, 25, 26], [23, 17, 22], [0, 0, 1], [0, 1]], ![[22, 9, 16], [20, 31], [3, 26, 39], [33, 32, 8], [17, 39, 9], [22, 31, 25]], ![[0, 1], [5, 18, 37], [8, 31, 17], [12, 33, 11], [3, 2, 31], [22, 9, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 35], []]
 b := ![[], [7, 35, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [38, 15, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1111264, 742264, -863132]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27104, 18104, -21052]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [11, 4, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 14, 17], [34, 28, 26], [0, 1]]
 g := ![![[5, 42, 11], [29, 41, 13], [42, 15], [7, 22, 1], []], ![[18, 34, 15, 36], [16, 17, 26, 17], [29, 9], [12, 13, 19, 41], [40, 31]], ![[30, 39, 15, 20], [4, 26, 1, 12], [4, 10], [0, 14, 21, 22], [31, 31]]]
 h' := ![![[31, 14, 17], [25, 28, 21], [6, 10, 20], [9, 31, 12], [0, 0, 1], [0, 1]], ![[34, 28, 26], [9, 15, 32], [29, 41, 42], [41, 22, 3], [5, 23, 28], [31, 14, 17]], ![[0, 1], [32, 0, 33], [5, 35, 24], [7, 33, 28], [41, 20, 14], [34, 28, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 20], []]
 b := ![[], [33, 28, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [11, 4, 21, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2863714, -1211955, 798553]
  a := ![3, -3, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66598, -28185, 18571]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419280633426640717485425502863952294, 5780787211855323099030081486947319, 18735716939578549324145135528720543]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![419280633426640717485425502863952294, 5780787211855323099030081486947319, 18735716939578549324145135528720543]] 
 ![![47, 0, 0], ![0, 47, 0], ![36, 22, 1]] where
  M :=![![![419280633426640717485425502863952294, 5780787211855323099030081486947319, 18735716939578549324145135528720543], ![1454211778771258944157235598685376449, 20049790483635858579347575273873572, 64982014634421134116385787424299095], ![707420652466959569163348171897031165, 9753487128088060189384237475150102, 31611364907346504777407738247768210]]]
  hmulB := by decide  
  f := ![![![-49626031841851310, 349501773255668, 28694362256663547]], ![![2210164897309604455, -652557141005041465, 31490376442708891]], ![![1005653687290183552, -301067107227987923, 22849514585552195]]]
  g := ![![![-5429897370174192727314880344042282, -8646914584231335362386444683934141, 18735716939578549324145135528720543], ![-18832781873785146468779845714667893, -29990521946247427488960420171504394, 64982014634421134116385787424299095], ![-9161457110585417081347455426013285, -14589288102841171168374170297356394, 31611364907346504777407738247768210]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [12, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 46], [0, 1]]
 g := ![![[16, 4], [15, 4], [31, 3], [32, 16], [1]], ![[0, 43], [46, 43], [19, 44], [15, 31], [1]]]
 h' := ![![[43, 46], [8, 2], [4, 45], [39, 12], [35, 43], [0, 1]], ![[0, 1], [0, 45], [12, 2], [38, 35], [4, 4], [43, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [6, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [12, 4, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![511619, 277017, -782424]
  a := ![-65, 1, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![610189, 372135, -782424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49626031841851310, 349501773255668, 28694362256663547]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-49626031841851310, 349501773255668, 28694362256663547]] 
 ![![47, 0, 0], ![11, 1, 0], ![10, 0, 1]] where
  M :=![![![-49626031841851310, 349501773255668, 28694362256663547], ![2210164897309604455, -652557141005041465, 31490376442708891], ![428632708133976094, 193520998558275801, -651858137458530129]]]
  hmulB := by decide  
  f := ![![![419280633426640717485425502863952294, 5780787211855323099030081486947319, 18735716939578549324145135528720543]], ![![129070186094985251840359917663592589, 1779541485405200269546350460219023, 5767551084463514397488984643409044]], ![![104260148653901420085480919160352215, 1437475728651942365525213879672836, 4658904985173021234443810500744120]]]
  g := ![![![-7242854764134024, 349501773255668, 28694362256663547], ![193050844339105780, -652557141005041465, 31490376442708891], ![102520916991026459, 193520998558275801, -651858137458530129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![419280633426640717485425502863952294, 5780787211855323099030081486947319, 18735716939578549324145135528720543]] ![![-49626031841851310, 349501773255668, 28694362256663547]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [30, 11, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 40, 51], [31, 12, 2], [0, 1]]
 g := ![![[43, 17, 13], [12, 28], [31, 21, 38], [3, 10], [1]], ![[30, 23, 50, 5], [34, 36], [21, 11, 20, 48], [40, 43], [47, 36, 5, 45]], ![[36, 22, 0, 34], [40, 9], [3, 43, 20, 34], [46, 17], [11, 26, 36, 8]]]
 h' := ![![[35, 40, 51], [4, 2, 15], [24, 49, 44], [15, 9, 12], [23, 42, 13], [0, 1]], ![[31, 12, 2], [4, 12, 17], [32, 8, 6], [9, 30, 20], [19, 24, 19], [35, 40, 51]], ![[0, 1], [9, 39, 21], [19, 49, 3], [47, 14, 21], [46, 40, 21], [31, 12, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 2], []]
 b := ![[], [48, 43, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [30, 11, 40, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5478133, 2685457, -2268453]
  a := ![-4, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-103361, 50669, -42801]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![244544984, 3371638, 10927587]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![244544984, 3371638, 10927587]] 
 ![![59, 0, 0], ![0, 59, 0], ![42, 13, 1]] where
  M :=![![![244544984, 3371638, 10927587], ![848167475, 11694019, 37900691], ![412602344, 5688711, 18437295]]]
  hmulB := by decide  
  f := ![![![4056, -1167, -5]], ![![-2719, 5328, -9341]], ![![764, 758, -2011]]]
  g := ![![![-3634130, -2350627, 10927587], ![-12604433, -8152796, 37900691], ![-6131594, -3966036, 18437295]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [51, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 58], [0, 1]]
 g := ![![[19, 22], [6, 4], [7], [0, 20], [34, 1]], ![[0, 37], [24, 55], [7], [31, 39], [9, 58]]]
 h' := ![![[34, 58], [48, 9], [56, 2], [0, 40], [36, 43], [0, 1]], ![[0, 1], [0, 50], [6, 57], [3, 19], [23, 16], [34, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [19, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [51, 25, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![155, 1530, -3268]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2329, 746, -3268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4056, -1167, -5]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![4056, -1167, -5]] 
 ![![59, 0, 0], ![13, 1, 0], ![25, 0, 1]] where
  M :=![![![4056, -1167, -5], ![-2719, 5328, -9341], ![-89929, 24472, 2994]]]
  hmulB := by decide  
  f := ![![![244544984, 3371638, 10927587]], ![![68258513, 941107, 3050158]], ![![110614016, 1525079, 4942830]]]
  g := ![![![328, -1167, -5], ![2738, 5328, -9341], ![-8185, 24472, 2994]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![244544984, 3371638, 10927587]] ![![4056, -1167, -5]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![345384715390819, -80293823072648, -39649533657674]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![345384715390819, -80293823072648, -39649533657674]] 
 ![![61, 0, 0], ![0, 61, 0], ![28, 56, 1]] where
  M :=![![![345384715390819, -80293823072648, -39649533657674], ![-3213601737786194, 1258318745274621, -682000118238858], ![-6737717847801332, 1408623548921890, 1097731099129325]]]
  hmulB := by decide  
  f := ![![![-38393066331542813037746297745, -529340325260045387836018340, -1715608988069575122060404058]], ![![-133160572731877375174323149146, -1835937256821690086641794187, -5950331590149938224748550778]], ![![-140930748543382447891659209148, -1943067730742983416741236578, -6297544895437482374851212919]]]
  g := ![![![23861830455831, 35083279700936, -39649533657674], ![260367238900030, 646726645354929, -682000118238858], ![-614330961039712, -984660950857710, 1097731099129325]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [47, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 60], [0, 1]]
 g := ![![[45, 13], [5], [9, 14], [4, 47], [20, 1]], ![[0, 48], [5], [45, 47], [29, 14], [40, 60]]]
 h' := ![![[20, 60], [25, 14], [4, 35], [56, 21], [36, 48], [0, 1]], ![[0, 1], [0, 47], [33, 26], [49, 40], [20, 13], [20, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [7, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [47, 41, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![94003, 56551, -151720]
  a := ![22, -1, 87]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![71183, 140211, -151720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38393066331542813037746297745, -529340325260045387836018340, -1715608988069575122060404058]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-38393066331542813037746297745, -529340325260045387836018340, -1715608988069575122060404058]] 
 ![![61, 0, 0], ![39, 1, 0], ![59, 0, 1]] where
  M :=![![![-38393066331542813037746297745, -529340325260045387836018340, -1715608988069575122060404058], ![-133160572731877375174323149146, -1835937256821690086641794187, -5950331590149938224748550778], ![-64777730877997546572219068992, -893116086026072709866443266, -2894617907341780862313830867]]]
  hmulB := by decide  
  f := ![![![345384715390819, -80293823072648, -39649533657674]], ![![168137740368127, -30707218927191, -36530031653904]], ![![223606235414049, -54569049383022, -20353957158581]]]
  g := ![![![1368395682782030971957741917, -529340325260045387836018340, -1715608988069575122060404058], ![4746074493492047433850349509, -1835937256821690086641794187, -5950331590149938224748550778], ![2308791032953841967034233435, -893116086026072709866443266, -2894617907341780862313830867]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![345384715390819, -80293823072648, -39649533657674]] ![![-38393066331542813037746297745, -529340325260045387836018340, -1715608988069575122060404058]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-132525373086565548990065608505048, -1827179509160931259995490713250, -5921947448823350317021062339543]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-132525373086565548990065608505048, -1827179509160931259995490713250, -5921947448823350317021062339543]] 
 ![![67, 0, 0], ![0, 67, 0], ![66, 19, 1]] where
  M :=![![![-132525373086565548990065608505048, -1827179509160931259995490713250, -5921947448823350317021062339543], ![-459644312577719836930612781571311, -6337297152114261072627808661395, -20539383522110800396984988045543], ![-223600086488918611457947657673852, -3082862449383895759242131398551, -9991656170436123592618790087895]]]
  hmulB := by decide  
  f := ![![![-1786410621956796, 704795837625471, -390029652947795]], ![![-28622691601729273, 5699416252321428, 5248337048055973]], ![![-9148139957106158, 2048873342039086, 1210230667851961]]]
  g := ![![![3855569530384710028855589640370, 1652086895798249623334398414001, -5921947448823350317021062339543], ![13372462684799895362244722827381, 5730014772656581290598312898566, -20539383522110800396984988045543], ![6505212250147246950073022210854, 2787441862520932126873356421962, -9991656170436123592618790087895]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [51, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 66], [0, 1]]
 g := ![![[55, 22], [48, 14], [26], [10], [14], [1]], ![[52, 45], [40, 53], [26], [10], [14], [1]]]
 h' := ![![[9, 66], [31, 42], [49, 58], [13, 19], [11, 12], [16, 9], [0, 1]], ![[0, 1], [7, 25], [35, 9], [50, 48], [52, 55], [30, 58], [9, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [13, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [51, 58, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![221, 22, 47]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, -13, 47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1786410621956796, -704795837625471, 390029652947795]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![1786410621956796, -704795837625471, 390029652947795]] 
 ![![67, 0, 0], ![48, 1, 0], ![3, 0, 1]] where
  M :=![![![1786410621956796, -704795837625471, 390029652947795], ![28622691601729273, -5699416252321428, -5248337048055973], ![-48808864355892137, 17530920160769456, -7109007927572370]]]
  hmulB := by decide  
  f := ![![![132525373086565548990065608505048, 1827179509160931259995490713250, 5921947448823350317021062339543]], ![![101803913742281584902294955071845, 1403610650624462112722557655185, 4549147180084053964387999706621]], ![![9271286652964406842211111689388, 127826880251741634913859754303, 414291022640390664831074285172]]]
  g := ![![![514127192076657, -704795837625471, 390029652947795], ![4745368400855608, -5699416252321428, -5248337048055973], ![-12969641914777745, 17530920160769456, -7109007927572370]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-132525373086565548990065608505048, -1827179509160931259995490713250, -5921947448823350317021062339543]] ![![1786410621956796, -704795837625471, 390029652947795]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5304216237158037904, -2292687874663098276, 1569219904398358163]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![5304216237158037904, -2292687874663098276, 1569219904398358163]] 
 ![![71, 0, 0], ![0, 71, 0], ![22, 35, 1]] where
  M :=![![![5304216237158037904, -2292687874663098276, 1569219904398358163], ![116244556889347381999, -25356713880544385243, -16772283092906428045], ![-154567887687481552970, 59130984698713570937, -29942089629870581795]]]
  hmulB := by decide  
  f := ![![![-24661895981118109839169073868343889850, -340023272104452254451981153637352441, -1102026340971941361110492479060892099]], ![![-85536074799048389314411883194963396505, -1179319548602889001396750654427803330, -3822212517807559396726341708159711627]], ![![-50393443525027352748091337753017085658, -694794251549424744100164808620235404, -2251850474893789892114838130797634385]]]
  g := ![![![-411529882529659742, -805850486318389211, 1569219904398358163], ![6834292745539278859, 7910890061565923892, -16772283092906428045], ![7100818086896778120, 15593015799213858222, -29942089629870581795]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [67, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 70], [0, 1]]
 g := ![![[37, 64], [62, 54], [67, 8], [45], [36], [1]], ![[66, 7], [31, 17], [44, 63], [45], [36], [1]]]
 h' := ![![[6, 70], [35, 63], [55, 57], [7, 47], [18, 51], [4, 6], [0, 1]], ![[0, 1], [58, 8], [42, 14], [5, 24], [40, 20], [40, 65], [6, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [52, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [67, 65, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-135, 4326, -6948]
  a := ![5, -2, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2151, 3486, -6948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24661895981118109839169073868343889850, 340023272104452254451981153637352441, 1102026340971941361110492479060892099]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![24661895981118109839169073868343889850, 340023272104452254451981153637352441, 1102026340971941361110492479060892099]] 
 ![![71, 0, 0], ![3, 1, 0], ![35, 0, 1]] where
  M :=![![![24661895981118109839169073868343889850, 340023272104452254451981153637352441, 1102026340971941361110492479060892099], ![85536074799048389314411883194963396505, 1179319548602889001396750654427803330, 3822212517807559396726341708159711627], ![41610160725650002648349443536928627343, 573695672610092184281843127041843432, 1859366092811793510300712961702508212]]]
  hmulB := by decide  
  f := ![![![-5304216237158037904, 2292687874663098276, -1569219904398358163]], ![![-1861369092969316841, 454010950768080001, 169924272953681036]], ![![-437741980465489770, 297367477668941813, -351839535550309210]]]
  g := ![![![-210268954495960486803578962812667478, 340023272104452254451981153637352441, 1102026340971941361110492479060892099], ![-729286224929927557397187726111407330, 1179319548602889001396750654427803330, 3822212517807559396726341708159711627], ![-354770979444972489648183654982882963, 573695672610092184281843127041843432, 1859366092811793510300712961702508212]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![5304216237158037904, -2292687874663098276, 1569219904398358163]] ![![24661895981118109839169073868343889850, 340023272104452254451981153637352441, 1102026340971941361110492479060892099]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2767104056316709697162767373843268640, -38151153350199678222485511937354035, -123649112809738931580739101881909157]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-2767104056316709697162767373843268640, -38151153350199678222485511937354035, -123649112809738931580739101881909157]] 
 ![![73, 0, 0], ![0, 73, 0], ![54, 61, 1]] where
  M :=![![![-2767104056316709697162767373843268640, -38151153350199678222485511937354035, -123649112809738931580739101881909157], ![-9597283993050297088161881868781713159, -132321533961992455744760722385822308, -428858339611336357360623197380741437], ![-4668726387301720265261731845522988893, -64369569313979278392977962488929364, -208623840662391812189731746260530378]]]
  hmulB := by decide  
  f := ![![![-248836949932920772, 99797347778364234, -57665781313199643]], ![![-4240670465559644043, 862347109865907497, 740713000913714229]], ![![-3633438614451599415, 760175694648136706, 590842228359540044]]]
  g := ![![![53560931991906748057495125038079806, 102800612712929796550720543874782254, -123649112809738931580739101881909157], ![185768032136463920675503709449018143, 356548454552459251277441839970402813, -428858339611336357360623197380741437], ![90369328883115583465531266473228103, 173447735768382483084666555608266078, -208623840662391812189731746260530378]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [64, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 72], [0, 1]]
 g := ![![[39, 8], [32], [70], [46, 9], [50], [1]], ![[0, 65], [32], [70], [66, 64], [50], [1]]]
 h' := ![![[59, 72], [53, 9], [38, 55], [49, 56], [20, 70], [9, 59], [0, 1]], ![[0, 1], [0, 64], [71, 18], [68, 17], [62, 3], [59, 14], [59, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [27, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [64, 14, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3169, 1575, -4785]
  a := ![-5, 0, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3583, 4020, -4785]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![248836949932920772, -99797347778364234, 57665781313199643]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![248836949932920772, -99797347778364234, 57665781313199643]] 
 ![![73, 0, 0], ![22, 1, 0], ![52, 0, 1]] where
  M :=![![![248836949932920772, -99797347778364234, 57665781313199643], ![4240670465559644043, -862347109865907497, -740713000913714229], ![-6877074840549251016, 2499404772538046415, -1061941805422635965]]]
  hmulB := by decide  
  f := ![![![2767104056316709697162767373843268640, 38151153350199678222485511937354035, 123649112809738931580739101881909157]], ![![965391414137231649667709097168953743, 13310231611868292830677287465857686, 43138887964734148659409362175106067]], ![![2035042976928364719420899113498259701, 28057938952388528026879788811388208, 90936680914641318553262534850956254]]]
  g := ![![![-7592356537389692, -99797347778364234, 57665781313199643], ![845607985344147245, -862347109865907497, -740713000913714229], ![-91000081567249342, 2499404772538046415, -1061941805422635965]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-2767104056316709697162767373843268640, -38151153350199678222485511937354035, -123649112809738931580739101881909157]] ![![248836949932920772, -99797347778364234, 57665781313199643]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19535146161899715894898163107824354915181, -269338753358358901078843985437525788350, -872935546465408864372327321324474016122]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-19535146161899715894898163107824354915181, -269338753358358901078843985437525788350, -872935546465408864372327321324474016122]] 
 ![![79, 0, 0], ![0, 79, 0], ![15, 34, 1]] where
  M :=![![![-19535146161899715894898163107824354915181, -269338753358358901078843985437525788350, -872935546465408864372327321324474016122], ![-67754714584553200358826891712859550818094, -934160932767770842000445374572874788269, -3027645573332280073003079204824680322922], ![-32960181659109359484283569377232121928658, -454435004732325127950567555083276557504, -1472838439484488644158133345447926364969]]]
  hmulB := by decide  
  f := ![![![-30330048639081916987, 6826083730050534578, 3944231246863505242]], ![![317357973468590972790, -119984988553266061647, 58552901087267781866]], ![![138177823455896766531, -51808056891940566668, 24602902336416356577]]]
  g := ![![![-81533075505298518092572826429838540169, 372284428183108132754180822020184693162, -872935546465408864372327321324474016122], ![-282785202336316446376970932158092987016, 1291212513424427235950686678347674129001, -3027645573332280073003079204824680322922], ![-137564621099266200277361635386243372837, 628127492882788465486404635318306580398, -1472838439484488644158133345447926364969]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [25, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 78], [0, 1]]
 g := ![![[45, 19], [70, 62], [7, 26], [71, 19], [45], [1]], ![[0, 60], [77, 17], [66, 53], [26, 60], [45], [1]]]
 h' := ![![[60, 78], [67, 16], [62, 33], [42, 37], [53, 16], [54, 60], [0, 1]], ![[0, 1], [0, 63], [67, 46], [50, 42], [65, 63], [20, 19], [60, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [42, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [25, 19, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10053, 730, -6898]
  a := ![-4, -2, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1437, 2978, -6898]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30330048639081916987, 6826083730050534578, 3944231246863505242]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-30330048639081916987, 6826083730050534578, 3944231246863505242]] 
 ![![79, 0, 0], ![43, 1, 0], ![51, 0, 1]] where
  M :=![![![-30330048639081916987, 6826083730050534578, 3944231246863505242], ![317357973468590972790, -119984988553266061647, 58552901087267781866], ![580827684669980235894, -115738139603016689444, -106332821093164992491]]]
  hmulB := by decide  
  f := ![![![-19535146161899715894898163107824354915181, -269338753358358901078843985437525788350, -872935546465408864372327321324474016122]], ![![-11490708855015708656195543105687428002163, -158426928192116501118870085422613717561, -513466760396770395455862709136418519192]], ![![-13028514378683479368659365669319926868391, -179629258557071254214830516612621414726, -582184193787599249710719325734127863129]]]
  g := ![![![-6645663830649286977, 6826083730050534578, 3944231246863505242], ![31525500326688287955, -119984988553266061647, 58552901087267781866], ![138994197004444462013, -115738139603016689444, -106332821093164992491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-19535146161899715894898163107824354915181, -269338753358358901078843985437525788350, -872935546465408864372327321324474016122]] ![![-30330048639081916987, 6826083730050534578, 3944231246863505242]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB188I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB188I1 : PrimesBelowBoundCertificateInterval O 31 79 188 where
  m := 11
  g := ![3, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB188I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
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
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
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
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
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
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I47N1, I59N1, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [], [], [I47N1], [], [I59N1], [I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
