
import IdealArithmetic.Examples.NF3_1_702351_1.RI3_1_702351_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181893580013295, 19129044488886, 11634898854700]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![181893580013295, 19129044488886, 11634898854700]] 
 ![![139, 0, 0], ![36, 1, 0], ![88, 0, 1]] where
  M :=![![![181893580013295, 19129044488886, 11634898854700], ![1911476804584472, 201022624502181, 122268412567502], ![2544570815394446, 267602673658100, 162764535524409]]]
  hmulB := by decide  
  f := ![![![-119830171, -4148374, 11682072]], ![![-17563808, -1966331, 2732618]], ![![-84534666, -693304, 6563601]]]
  g := ![![![-11011677128059, 19129044488886, 11634898854700], ![-115719122182980, 201022624502181, 122268412567502], ![-154046075988814, 267602673658100, 162764535524409]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, -2, -3]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![63, -2, -3]] 
 ![![139, 0, 0], ![119, 1, 0], ![85, 0, 1]] where
  M :=![![![63, -2, -3], ![-487, 61, -11], ![-184, -69, 65]]]
  hmulB := by decide  
  f := ![![![3206, 337, 205]], ![![2987, 314, 191]], ![![2283, 240, 146]]]
  g := ![![![4, -2, -3], ![-49, 61, -11], ![18, -69, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1556652, -3689, -108503]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![1556652, -3689, -108503]] 
 ![![139, 0, 0], ![123, 1, 0], ![105, 0, 1]] where
  M :=![![![1556652, -3689, -108503], ![-17476361, 1552963, 82680], ![4397209, -2495569, 1560341]]]
  hmulB := by decide  
  f := ![![![-2629485485303, -276532821156, -168196137869]], ![![-2525606895910, -265608311573, -161551500490]], ![![-2250940559863, -236722715053, -143982353528]]]
  g := ![![![96426, -3689, -108503], ![-1562390, 1552963, 82680], ![1061269, -2495569, 1560341]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![181893580013295, 19129044488886, 11634898854700]] ![![63, -2, -3]]
  ![![2629485485303, 276532821156, 168196137869]] where
 M := ![![![2629485485303, 276532821156, 168196137869]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![2629485485303, 276532821156, 168196137869]] ![![1556652, -3689, -108503]]
  ![![139, 0, 0]] where
 M := ![![![-139, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [72, 46, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 73, 90], [107, 75, 59], [0, 1]]
 g := ![![[74, 117, 16], [15, 130], [100, 53, 20], [143, 36], [134, 88, 100], [143, 1], []], ![[148, 102, 86, 79], [124, 118], [21, 63, 70, 32], [72, 145], [98, 130, 110, 83], [8, 112], [2, 54]], ![[72, 32, 65, 141], [46, 110], [60, 68, 4, 138], [10, 45], [112, 47, 11, 44], [15, 114], [33, 54]]]
 h' := ![![[36, 73, 90], [32, 8, 4], [101, 97, 117], [13, 22, 136], [37, 92, 6], [134, 55, 139], [0, 0, 1], [0, 1]], ![[107, 75, 59], [11, 26, 126], [105, 72, 72], [133, 67, 111], [129, 68, 88], [130, 46, 28], [109, 84, 75], [36, 73, 90]], ![[0, 1], [79, 115, 19], [115, 129, 109], [42, 60, 51], [100, 138, 55], [70, 48, 131], [133, 65, 73], [107, 75, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 114], []]
 b := ![[], [132, 116, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [72, 46, 6, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1279165, -6854, -23989]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8585, -46, -161]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-902635953375716109, -94926733027795988, -57737485948511993]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-902635953375716109, -94926733027795988, -57737485948511993]] 
 ![![151, 0, 0], ![0, 151, 0], ![145, 96, 1]] where
  M :=![![![-902635953375716109, -94926733027795988, -57737485948511993], ![-9485588703766022849, -997562686403512097, -606749645246059923], ![-12627279663843602390, -1327962176815775839, -807709220347920121]]]
  hmulB := by decide  
  f := ![![![129247660, -88628229, 57338347]], ![![9054217409, 40619431, -677735950]], ![![5768470683, -50548648, -374375596]]]
  g := ![![![49465559663301476, 36078621973704340, -57737485948511993], ![519821919582203086, 379141743425286361, -606749645246059923], ![691990445606654405, 504716046202546727, -807709220347920121]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [125, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 150], [0, 1]]
 g := ![![[71, 29], [25, 94], [0, 18], [84], [], [99], [1]], ![[0, 122], [50, 57], [8, 133], [84], [], [99], [1]]]
 h' := ![![[34, 150], [46, 123], [0, 83], [70, 138], [0, 50], [79], [26, 34], [0, 1]], ![[0, 1], [0, 28], [104, 68], [81, 13], [39, 101], [79], [125, 117], [34, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [111, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [125, 117, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14169, 7452, 2286]
  a := ![5, 0, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2289, -1404, 2286]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-129247660, 88628229, -57338347]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-129247660, 88628229, -57338347]] 
 ![![151, 0, 0], ![84, 1, 0], ![102, 0, 1]] where
  M :=![![![-129247660, 88628229, -57338347], ![-9054217409, -40619431, 677735950], ![16906708831, -1318781981, -217875889]]]
  hmulB := by decide  
  f := ![![![902635953375716109, 94926733027795988, 57737485948511993]], ![![564947078061762755, 59413299739989239, 36137075926629585]], ![![693351966279249308, 72917145335436865, 44350548258914857]]]
  g := ![![![-11427202, 88628229, -57338347], ![-495173855, -40619431, 677735950], ![992766463, -1318781981, -217875889]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-902635953375716109, -94926733027795988, -57737485948511993]] ![![-129247660, 88628229, -57338347]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [37, 122, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 152, 152], [1, 4, 5], [0, 1]]
 g := ![![[86, 112, 67], [35, 153], [152, 85, 11], [137, 119, 3], [24, 105, 121], [116, 1], []], ![[27, 44, 73, 104], [45, 35], [24, 155, 13, 72], [70, 153, 60, 104], [35, 23, 66, 94], [37, 16], [124, 25]], ![[132, 121, 24, 45], [150, 16], [133, 38, 87, 54], [117, 64, 18, 104], [69, 28, 114, 62], [116, 25], [114, 25]]]
 h' := ![![[115, 152, 152], [117, 131, 99], [28, 118, 56], [112, 11, 110], [54, 78, 72], [104, 98, 146], [0, 0, 1], [0, 1]], ![[1, 4, 5], [151, 12, 55], [51, 22, 105], [27, 93, 71], [62, 38, 55], [48, 29, 94], [2, 67, 4], [115, 152, 152]], ![[0, 1], [71, 14, 3], [122, 17, 153], [31, 53, 133], [146, 41, 30], [117, 30, 74], [22, 90, 152], [1, 4, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 29], []]
 b := ![[], [124, 56, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [37, 122, 41, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29793139854, -363743723, -684880315]
  a := ![-66, -64, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-189765222, -2316839, -4362295]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1355320, 341246, -159461]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-1355320, 341246, -159461]] 
 ![![163, 0, 0], ![37, 1, 0], ![9, 0, 1]] where
  M :=![![![-1355320, 341246, -159461], ![-24990729, -1014074, 2548183], ![62275812, -3667603, -1696566]]]
  hmulB := by decide  
  f := ![![![-11066167085233, -1163786003219, -707852001904]], ![![-3225398321881, -339202669985, -206313951479]], ![![-1560759866244, -164139080201, -99834657050]]]
  g := ![![![-76971, 341246, -159461], ![-63826, -1014074, 2548183], ![1308259, -3667603, -1696566]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1348068610, -134539374, 4701723]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![1348068610, -134539374, 4701723]] 
 ![![163, 0, 0], ![41, 1, 0], ![57, 0, 1]] where
  M :=![![![1348068610, -134539374, 4701723], ![487898655, 1213529236, -946477341], ![-21877118472, 108139629, 1482607984]]]
  hmulB := by decide  
  f := ![![![1901539842623666713, 199977592635642783, 121632790643250906]], ![![600895509364447955, 63193857259635973, 38436532356929667]], ![![828153712112257356, 87093723711818463, 52973198261676844]]]
  g := ![![![40467391, -134539374, 4701723], ![28726432, 1213529236, -946477341], ![-679874223, 108139629, 1482607984]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-692117, 21372, 33420]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![-692117, 21372, 33420]] 
 ![![163, 0, 0], ![85, 1, 0], ![97, 0, 1]] where
  M :=![![![-692117, 21372, 33420], ![5423364, -670745, 116184], ![1903572, 768660, -713489]]]
  hmulB := by decide  
  f := ![![![389263185865, 40937304108, 24899382348]], ![![228086171563, 23986940731, 14589627276]], ![![265055603695, 27874872960, 16954392451]]]
  g := ![![![-35279, 21372, 33420], ![313907, -670745, 116184], ![35435, 768660, -713489]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-1355320, 341246, -159461]] ![![1348068610, -134539374, 4701723]]
  ![![1827976304582522, 579211848657767, -565772097659870]] where
 M := ![![![1827976304582522, 579211848657767, -565772097659870]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![1827976304582522, 579211848657767, -565772097659870]] ![![-692117, 21372, 33420]]
  ![![163, 0, 0]] where
 M := ![![![799115288898646433474, -784322322433651940431, 532058285710844872798]]]
 hmul := by decide  
 g := ![![![![4902547784654272598, -4811793389163508837, 3264161262029723146]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40943, -817, -2313]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![40943, -817, -2313]] 
 ![![167, 0, 0], ![0, 167, 0], ![108, 141, 1]] where
  M :=![![![40943, -817, -2313], ![-374027, 40126, -3406], ![-25139, -53199, 41760]]]
  hmulB := by decide  
  f := ![![![8948898, 941121, 572420]], ![![94041862, 9890019, 6015427]], ![![85937561, 9037721, 5497032]]]
  g := ![![![1741, 1948, -2313], ![-37, 3116, -3406], ![-27157, -35577, 41760]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [58, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 166], [0, 1]]
 g := ![![[51, 72], [30, 62], [21, 162], [124], [44], [148, 133], [1]], ![[0, 95], [0, 105], [115, 5], [124], [44], [19, 34], [1]]]
 h' := ![![[48, 166], [97, 78], [118, 88], [136, 117], [100, 142], [100, 82], [109, 48], [0, 1]], ![[0, 1], [0, 89], [0, 79], [74, 50], [69, 25], [28, 85], [75, 119], [48, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [40, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [58, 119, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9618, 7344, -1991]
  a := ![-5, -1, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1230, 1725, -1991]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8948898, -941121, -572420]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-8948898, -941121, -572420]] 
 ![![167, 0, 0], ![16, 1, 0], ![33, 0, 1]] where
  M :=![![![-8948898, -941121, -572420], ![-94041862, -9890019, -6015427], ![-125189161, -13165660, -8007777]]]
  hmulB := by decide  
  f := ![![![-40943, 817, 2313]], ![![-1683, -162, 242]], ![![-7940, 480, 207]]]
  g := ![![![149694, -941121, -572420], ![1573099, -9890019, -6015427], ![2094120, -13165660, -8007777]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![40943, -817, -2313]] ![![-8948898, -941121, -572420]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1141, 120, 73]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![1141, 120, 73]] 
 ![![173, 0, 0], ![13, 1, 0], ![172, 0, 1]] where
  M :=![![![1141, 120, 73], ![11993, 1261, 767], ![15962, 1679, 1021]]]
  hmulB := by decide  
  f := ![![![-312, 47, -13]], ![![-35, 2, 1]], ![![-263, 45, -15]]]
  g := ![![![-75, 120, 73], ![-788, 1261, 767], ![-1049, 1679, 1021]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-162332695, 16412502, -725011]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-162332695, 16412502, -725011]] 
 ![![173, 0, 0], ![29, 1, 0], ![49, 0, 1]] where
  M :=![![![-162332695, 16412502, -725011], ![-83901767, -145920193, 115612525], ![2675763328, -16675253, -178745197]]]
  hmulB := by decide  
  f := ![![![-28010401748406846, -2945745645105677, -1791697052740427]], ![![-6396857615521495, -672732780933972, -409177670476715]], ![![-10198593468831733, -1072546640596578, -652357292991804]]]
  g := ![![![-3484218, 16412502, -725011], ![-8770115, -145920193, 115612525], ![68889366, -16675253, -178745197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8182344256660, -860505507108, -523387069591]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![-8182344256660, -860505507108, -523387069591]] 
 ![![173, 0, 0], ![131, 1, 0], ![125, 0, 1]] where
  M :=![![![-8182344256660, -860505507108, -523387069591], ![-85986329218367, -9042849763768, -5500151480165], ![-114465581443202, -12037902600593, -7321838749552]]]
  hmulB := by decide  
  f := ![![![40905909, -1051847, -2133932]], ![![28976921, -566115, -1646093]], ![![29144810, -1043707, -1299328]]]
  g := ![![![982469716031, -860505507108, -523387069591], ![10324542918242, -9042849763768, -5500151480165], ![13744101172997, -12037902600593, -7321838749552]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![1141, 120, 73]] ![![-162332695, 16412502, -725011]]
  ![![40905909, -1051847, -2133932]] where
 M := ![![![40905909, -1051847, -2133932]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![40905909, -1051847, -2133932]] ![![-8182344256660, -860505507108, -523387069591]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [51, 20, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 31, 23], [142, 147, 156], [0, 1]]
 g := ![![[38, 49, 39], [162, 147, 117], [111, 39], [33, 27], [15, 141, 13], [16, 173, 1], []], ![[27, 10, 27, 103], [64, 169, 81, 130], [144, 151], [134, 48], [142, 92, 40, 38], [104, 101, 166, 103], [42, 171]], ![[161, 73, 156, 139], [8, 30, 110, 59], [102, 80], [43, 147], [66, 164, 36, 145], [8, 35, 25, 93], [88, 171]]]
 h' := ![![[31, 31, 23], [151, 32, 24], [71, 71, 98], [2, 175, 24], [130, 3, 122], [79, 165, 152], [0, 0, 1], [0, 1]], ![[142, 147, 156], [7, 57, 147], [20, 9, 108], [174, 15, 35], [57, 9, 103], [28, 148, 5], [72, 58, 147], [31, 31, 23]], ![[0, 1], [7, 90, 8], [20, 99, 152], [116, 168, 120], [55, 167, 133], [143, 45, 22], [103, 121, 31], [142, 147, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116, 118], []]
 b := ![[], [121, 47, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [51, 20, 6, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1279134, -6802, -23807]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7146, -38, -133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-923855, 62962, 18743]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-923855, 62962, 18743]] 
 ![![181, 0, 0], ![0, 181, 0], ![92, 83, 1]] where
  M :=![![![-923855, 62962, 18743], ![3143547, -860893, 421991], ![9274704, 431089, -986817]]]
  hmulB := by decide  
  f := ![![![3688553422, 387910901, 235939861]], ![![38762139423, 4076464323, 2479436446]], ![![19934833748, 2096469384, 1275139971]]]
  g := ![![![-14631, -8247, 18743], ![-197125, -198266, 421991], ![552828, 454900, -986817]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [15, 137, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 180], [0, 1]]
 g := ![![[166, 169], [101], [122, 145], [152], [118, 145], [61, 126], [1]], ![[0, 12], [101], [167, 36], [152], [163, 36], [175, 55], [1]]]
 h' := ![![[44, 180], [152, 13], [161, 61], [44, 114], [40, 40], [171, 114], [166, 44], [0, 1]], ![[0, 1], [0, 168], [130, 120], [173, 67], [171, 141], [119, 67], [111, 137], [44, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [159]]
 b := ![[], [61, 170]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [15, 137, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![64337, 5744, 4097]
  a := ![3, 21, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1727, -1847, 4097]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3688553422, 387910901, 235939861]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![3688553422, 387910901, 235939861]] 
 ![![181, 0, 0], ![144, 1, 0], ![172, 0, 1]] where
  M :=![![![3688553422, 387910901, 235939861], ![38762139423, 4076464323, 2479436446], ![51600421455, 5426616803, 3300642521]]]
  hmulB := by decide  
  f := ![![![-923855, 62962, 18743]], ![![-717633, 45335, 17243]], ![![-826676, 62213, 12359]]]
  g := ![![![-512443494, 387910901, 235939861], ![-5385148021, 4076464323, 2479436446], ![-7168745369, 5426616803, 3300642521]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-923855, 62962, 18743]] ![![3688553422, 387910901, 235939861]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [61, 103, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 92, 137], [58, 98, 54], [0, 1]]
 g := ![![[142, 10, 100], [155, 32, 134], [55, 179, 51], [188, 137, 25], [175, 18, 39], [169, 182, 1], []], ![[136, 91, 81, 122], [69, 139, 16, 132], [40, 95, 101, 28], [123, 51, 28, 57], [49, 186, 152, 55], [52, 173, 78, 140], [110, 51]], ![[90, 178, 173, 2], [106, 60, 94, 10], [189, 114, 2, 2], [144, 128, 164, 86], [117, 25, 86, 65], [124, 0, 138, 184], [2, 51]]]
 h' := ![![[124, 92, 137], [95, 50, 181], [83, 97, 158], [183, 33, 137], [21, 2, 186], [5, 141, 109], [0, 0, 1], [0, 1]], ![[58, 98, 54], [46, 115, 140], [27, 140, 123], [59, 18, 184], [105, 138, 166], [16, 70, 12], [71, 162, 98], [124, 92, 137]], ![[0, 1], [180, 26, 61], [144, 145, 101], [75, 140, 61], [162, 51, 30], [189, 171, 70], [186, 29, 92], [58, 98, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 133], []]
 b := ![[], [134, 19, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [61, 103, 9, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3683435, -11651, 116510]
  a := ![-3, 1, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19285, -61, 610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [94, 14, 181, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 137, 62], [187, 55, 131], [0, 1]]
 g := ![![[123, 21, 170], [147, 170], [142, 118], [92, 36], [12, 134], [41, 144], [1]], ![[29, 33, 144, 7], [32, 175], [59, 18], [103, 107], [78, 192], [139, 32], [109, 140, 48, 166]], ![[141, 35, 12, 139], [67, 109], [140, 134], [166, 7], [5, 69], [143, 9], [182, 48, 0, 27]]]
 h' := ![![[18, 137, 62], [72, 130, 39], [103, 2, 154], [83, 23, 73], [168, 157, 187], [157, 102, 83], [99, 179, 12], [0, 1]], ![[187, 55, 131], [192, 130, 169], [43, 5, 102], [68, 37, 37], [10, 104, 140], [104, 22, 81], [25, 169, 178], [18, 137, 62]], ![[0, 1], [53, 126, 178], [102, 186, 130], [157, 133, 83], [163, 125, 59], [61, 69, 29], [46, 38, 3], [187, 55, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146, 20], []]
 b := ![[], [149, 93, 174], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [94, 14, 181, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11088429, 896678, 112133]
  a := ![4, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![57453, 4646, 581]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀



lemma PB238I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB238I3 : PrimesBelowBoundCertificateInterval O 137 193 238 where
  m := 11
  g := ![3, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB238I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
    · exact ![I193N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![163, 163, 163]
    · exact ![27889, 167]
    · exact ![173, 173, 173]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![6967871]
    · exact ![7189057]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N0, I139N1, I139N2, I151N1, I163N0, I163N1, I163N2, I167N1, I173N0, I173N1, I173N2, I181N1]
  Il := ![[I139N0, I139N1, I139N2], [], [I151N1], [], [I163N0, I163N1, I163N2], [I167N1], [I173N0, I173N1, I173N2], [], [I181N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
