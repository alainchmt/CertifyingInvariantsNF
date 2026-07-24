
import IdealArithmetic.Examples.NF3_1_735727_1.RI3_1_735727_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 53, -9]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-41, 53, -9]] 
 ![![197, 0, 0], ![0, 197, 0], ![114, 16, 1]] where
  M :=![![![-41, 53, -9], ![-459, 454, 53], ![2703, -3374, 454]]]
  hmulB := by decide  
  f := ![![![-1954, -32, -35]], ![![-1785, -29, -32]], ![![-1284, -21, -23]]]
  g := ![![![5, 1, -9], ![-33, -2, 53], ![-249, -54, 454]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [57, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [185, 196], [0, 1]]
 g := ![![[135, 37], [144], [81, 148], [134], [92], [83], [185, 1]], ![[85, 160], [144], [78, 49], [134], [92], [83], [173, 196]]]
 h' := ![![[185, 196], [173, 148], [111, 12], [84, 99], [165, 118], [175, 17], [93, 87], [0, 1]], ![[0, 1], [170, 49], [164, 185], [78, 98], [128, 79], [168, 180], [34, 110], [185, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [169, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [57, 12, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![159, -71, -66]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39, 5, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1954, -32, -35]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-1954, -32, -35]] 
 ![![197, 0, 0], ![181, 1, 0], ![138, 0, 1]] where
  M :=![![![-1954, -32, -35], ![-1785, -29, -32], ![-1632, -25, -29]]]
  hmulB := by decide  
  f := ![![![-41, 53, -9]], ![![-40, 51, -8]], ![![-15, 20, -4]]]
  g := ![![![44, -32, -35], ![40, -29, -32], ![35, -25, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-41, 53, -9]] ![![-1954, -32, -35]]
  ![![197, 0, 0]] where
 M := ![![![197, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4201, -3325, -1395]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![4201, -3325, -1395]] 
 ![![199, 0, 0], ![6, 1, 0], ![163, 0, 1]] where
  M :=![![![4201, -3325, -1395], ![-71145, 80926, -3325], ![-169575, 111730, 80926]]]
  hmulB := by decide  
  f := ![![![-6920519726, -113215600, -123947395]], ![![-240424299, -3933199, -4306030]], ![![-5697581462, -93209055, -102044414]]]
  g := ![![![1264, -3325, -1395], ![-74, 80926, -3325], ![-70507, 111730, 80926]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12122, -17291, 4401]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![12122, -17291, 4401]] 
 ![![199, 0, 0], ![49, 1, 0], ![186, 0, 1]] where
  M :=![![![12122, -17291, 4401], ![224451, -229933, -17291], ![-881841, 1175456, -229933]]]
  hmulB := by decide  
  f := ![![![73193994185, 1197410353, 1310913814]], ![![18358604621, 300335888, 328804961]], ![![68719350987, 1124207843, 1230772381]]]
  g := ![![![205, -17291, 4401], ![73906, -229933, -17291], ![-78953, 1175456, -229933]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2621502018945007105, -42886218915189017, -46951437045201511]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![-2621502018945007105, -42886218915189017, -46951437045201511]] 
 ![![199, 0, 0], ![144, 1, 0], ![159, 0, 1]] where
  M :=![![![-2621502018945007105, -42886218915189017, -46951437045201511], ![-2394523289305277061, -39172981458924000, -42886218915189017], ![-2187197164674639867, -35781248969881126, -39172981458924000]]]
  hmulB := by decide  
  f := ![![![534793142, -947873386, 396737711]], ![![488662491, -792862053, 282323402]], ![![184374708, -393694517, 210027714]]]
  g := ![![![55373829120750008, -42886218915189017, -46951437045201511], ![50579371096958958, -39172981458924000, -42886218915189017], ![46200033864106323, -35781248969881126, -39172981458924000]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![4201, -3325, -1395]] ![![12122, -17291, 4401]]
  ![![534793142, -947873386, 396737711]] where
 M := ![![![534793142, -947873386, 396737711]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![534793142, -947873386, 396737711]] ![![-2621502018945007105, -42886218915189017, -46951437045201511]]
  ![![199, 0, 0]] where
 M := ![![![199, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [81, 119, 122, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 141, 132], [193, 69, 79], [0, 1]]
 g := ![![[168, 140, 173], [102, 162, 170], [172, 51], [4, 182], [22, 23, 55], [147, 114], [1]], ![[159, 71, 3, 149], [168, 121, 196, 118], [72, 101], [62, 139], [204, 65, 102, 110], [119, 120], [167, 139, 55, 68]], ![[73, 18, 19, 54], [167, 149, 31, 37], [113, 24], [25, 150], [88, 63, 141, 171], [12, 78], [74, 45, 1, 143]]]
 h' := ![![[107, 141, 132], [178, 185, 54], [114, 172, 35], [72, 194, 85], [117, 138, 56], [140, 147, 104], [130, 92, 89], [0, 1]], ![[193, 69, 79], [150, 141, 83], [47, 28, 10], [56, 114, 34], [15, 196, 136], [73, 207, 205], [165, 151, 139], [107, 141, 132]], ![[0, 1], [58, 96, 74], [177, 11, 166], [62, 114, 92], [71, 88, 19], [183, 68, 113], [201, 179, 194], [193, 69, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 185], []]
 b := ![[], [95, 67, 208], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [81, 119, 122, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![148544, -179139, 18146]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![704, -849, 86]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![644867912136295, 10549656743117, 11549666931526]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![644867912136295, 10549656743117, 11549666931526]] 
 ![![223, 0, 0], ![0, 223, 0], ![62, 26, 1]] where
  M :=![![![644867912136295, 10549656743117, 11549666931526], ![589033013507826, 9636230902365, 10549656743117], ![538032493898967, 8801892636391, 9636230902365]]]
  hmulB := by decide  
  f := ![![![1747186, -2242193, 360613]], ![![18391263, -18086529, -2242193]], ![![2117249, -2096654, -242267]]]
  g := ![![![-319333800979, -1299290060433, 11549666931526], ![-291684773836, -1186793024299, 10549656743117], ![-266429695281, -1084036371413, 9636230902365]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [222, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [186, 222], [0, 1]]
 g := ![![[186, 203], [158, 144], [210, 210], [92, 166], [181, 76], [132], [186, 1]], ![[34, 20], [182, 79], [22, 13], [194, 57], [45, 147], [132], [149, 222]]]
 h' := ![![[186, 222], [158, 42], [210, 12], [92, 87], [181, 101], [163, 107], [186, 32], [0, 1]], ![[0, 1], [165, 181], [212, 211], [218, 136], [12, 122], [218, 116], [117, 191], [186, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [120, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [222, 37, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1848, 70, 37]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -4, 37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1747186, 2242193, -360613]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-1747186, 2242193, -360613]] 
 ![![223, 0, 0], ![197, 1, 0], ![216, 0, 1]] where
  M :=![![![-1747186, 2242193, -360613], ![-18391263, 18086529, 2242193], ![114351843, -141711878, 18086529]]]
  hmulB := by decide  
  f := ![![![-644867912136295, -10549656743117, -11549666931526]], ![![-572322922441067, -9362863718818, -10250376871093]], ![![-627038123387169, -10257971969281, -11230333130547]]]
  g := ![![![-1639313, 2242193, -360613], ![-18232068, 18086529, 2242193], ![108183415, -141711878, 18086529]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![644867912136295, 10549656743117, 11549666931526]] ![![-1747186, 2242193, -360613]]
  ![![223, 0, 0]] where
 M := ![![![-223, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8862974, 144993, 158737]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![8862974, 144993, 158737]] 
 ![![227, 0, 0], ![50, 1, 0], ![224, 0, 1]] where
  M :=![![![8862974, 144993, 158737], ![8095587, 132439, 144993], ![7394643, 120972, 132439]]]
  hmulB := by decide  
  f := ![![![-4475, 4437, 506]], ![![-872, 835, 131]], ![![-3419, 3417, 357]]]
  g := ![![![-149532, 144993, 158737], ![-136585, 132439, 144993], ![-124759, 120972, 132439]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N0 : Nat.card (O ⧸ I227N0) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N0)

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := prime_ideal_of_norm_prime hp227.out _ NI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![244748, -107878, -175243]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![244748, -107878, -175243]] 
 ![![227, 0, 0], ![81, 1, 0], ![22, 0, 1]] where
  M :=![![![244748, -107878, -175243], ![-8937393, 9883113, -107878], ![-5501778, -3004103, 9883113]]]
  hmulB := by decide  
  f := ![![![97351845947335, 1592618486243, 1743584034343]], ![![35129613689364, 574699653939, 629175882238]], ![![9792793628369, 160204298262, 175390188608]]]
  g := ![![![56556, -107878, -175243], ![-3555490, 9883113, -107878], ![89877, -3004103, 9883113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10665362, 174479, 191018]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![10665362, 174479, 191018]] 
 ![![227, 0, 0], ![96, 1, 0], ![91, 0, 1]] where
  M :=![![![10665362, 174479, 191018], ![9741918, 159372, 174479], ![8898429, 145573, 159372]]]
  hmulB := by decide  
  f := ![![![2917, -3874, 745]], ![![1401, -1806, 298]], ![![299, -447, 131]]]
  g := ![![![-103380, 174479, 191018], ![-94429, 159372, 174479], ![-86253, 145573, 159372]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![8862974, 144993, 158737]] ![![244748, -107878, -175243]]
  ![![2917, -3874, 745]] where
 M := ![![![2917, -3874, 745]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![2917, -3874, 745]] ![![10665362, 174479, 191018]]
  ![![227, 0, 0]] where
 M := ![![![227, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-355, 501, -123]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-355, 501, -123]] 
 ![![229, 0, 0], ![0, 229, 0], ![163, 197, 1]] where
  M :=![![![-355, 501, -123], ![-6273, 6410, 501], ![25551, -33828, 6410]]]
  hmulB := by decide  
  f := ![![![-253432, -4146, -4539]], ![![-231489, -3787, -4146]], ![![-380455, -6224, -6814]]]
  g := ![![![86, 108, -123], ![-384, -403, 501], ![-4451, -5662, 6410]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [132, 228, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 228], [0, 1]]
 g := ![![[85, 144], [43], [190, 97], [209], [42], [220, 215], [1, 1]], ![[0, 85], [43], [58, 132], [209], [42], [206, 14], [2, 228]]]
 h' := ![![[1, 228], [12, 217], [110, 57], [166, 201], [198, 74], [43, 27], [97, 98], [0, 1]], ![[0, 1], [0, 12], [167, 172], [138, 28], [43, 155], [70, 202], [195, 131], [1, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166]]
 b := ![[], [73, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [132, 228, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55, 1019, -1184]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![843, 1023, -1184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-253432, -4146, -4539]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-253432, -4146, -4539]] 
 ![![229, 0, 0], ![32, 1, 0], ![121, 0, 1]] where
  M :=![![![-253432, -4146, -4539], ![-231489, -3787, -4146], ![-211446, -3459, -3787]]]
  hmulB := by decide  
  f := ![![![-355, 501, -123]], ![![-77, 98, -15]], ![![-76, 117, -37]]]
  g := ![![![1871, -4146, -4539], ![1709, -3787, -4146], ![1561, -3459, -3787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-355, 501, -123]] ![![-253432, -4146, -4539]]
  ![![229, 0, 0]] where
 M := ![![![229, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 4, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![71, 4, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![71, 4, 1]] where
  M :=![![![71, 4, 1], ![51, 16, 4], ![204, -169, 16]]]
  hmulB := by decide  
  f := ![![![4, -1, 0]], ![![0, 4, -1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![-1, 0, 4], ![-4, -1, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [168, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [130, 232], [0, 1]]
 g := ![![[2, 60], [229], [232], [46, 29], [38], [176, 72], [130, 1]], ![[113, 173], [229], [232], [88, 204], [38], [216, 161], [27, 232]]]
 h' := ![![[130, 232], [75, 35], [58, 55], [194, 144], [203, 31], [23, 182], [62, 189], [0, 1]], ![[0, 1], [198, 198], [218, 178], [41, 89], [39, 202], [150, 51], [167, 44], [130, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [216]]
 b := ![[], [203, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [168, 103, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![270, -162, -157]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49, 2, -157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-4, 1, 0]] 
 ![![233, 0, 0], ![229, 1, 0], ![217, 0, 1]] where
  M :=![![![-4, 1, 0], ![0, -4, 1], ![51, -55, -4]]]
  hmulB := by decide  
  f := ![![![-71, -4, -1]], ![![-70, -4, -1]], ![![-67, -3, -1]]]
  g := ![![![-1, 1, 0], ![3, -4, 1], ![58, -55, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![71, 4, 1]] ![![-4, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![-233, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1129797689339344, -18482820415443, -20234821373961]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-1129797689339344, -18482820415443, -20234821373961]] 
 ![![239, 0, 0], ![0, 239, 0], ![212, 184, 1]] where
  M :=![![![-1129797689339344, -18482820415443, -20234821373961], ![-1031975890072011, -16882513771489, -18482820415443], ![-942623841187593, -15420767222646, -16882513771489]]]
  hmulB := by decide  
  f := ![![![370063, 145539, -602880]], ![![-30746880, 33528463, 145539]], ![![-23311925, 25779665, -282439]]]
  g := ![![![13221692225692, 15500938545579, -20234821373961], ![12076912292895, 14158813567657, -18482820415443], ![11031251373925, 12932894421470, -16882513771489]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [113, 176, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 238], [0, 1]]
 g := ![![[120, 55], [162, 134], [191, 68], [93, 133], [34], [139, 68], [63, 1]], ![[0, 184], [0, 105], [173, 171], [107, 106], [34], [121, 171], [126, 238]]]
 h' := ![![[63, 238], [97, 154], [166, 96], [7, 32], [169, 206], [67, 89], [51, 32], [0, 1]], ![[0, 1], [0, 85], [0, 143], [111, 207], [2, 33], [177, 150], [155, 207], [63, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [225]]
 b := ![[], [101, 232]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [113, 176, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2228, 1343, 484]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-420, -367, 484]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-370063, -145539, 602880]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-370063, -145539, 602880]] 
 ![![239, 0, 0], ![55, 1, 0], ![82, 0, 1]] where
  M :=![![![-370063, -145539, 602880], ![30746880, -33528463, -145539], ![-7422489, 38751525, -33528463]]]
  hmulB := by decide  
  f := ![![![1129797689339344, 18482820415443, 20234821373961]], ![![264313174911029, 4324006847786, 4733882828382]], ![![391573365552359, 6405908122548, 7013129148269]]]
  g := ![![![-174902, -145539, 602880], ![7894337, -33528463, -145539], ![2554718, 38751525, -33528463]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-1129797689339344, -18482820415443, -20234821373961]] ![![-370063, -145539, 602880]]
  ![![239, 0, 0]] where
 M := ![![![-239, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1064035, 17407, 19057]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![1064035, 17407, 19057]] 
 ![![241, 0, 0], ![0, 241, 0], ![135, 70, 1]] where
  M :=![![![1064035, 17407, 19057], ![971907, 15900, 17407], ![887757, 14522, 15900]]]
  hmulB := by decide  
  f := ![![![106, -106, -11]], ![![-561, 711, -106]], ![![-126, 169, -34]]]
  g := ![![![-6260, -5463, 19057], ![-5718, -4990, 17407], ![-5223, -4558, 15900]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [93, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [219, 240], [0, 1]]
 g := ![![[192, 141], [121], [90], [1], [124, 160], [228, 87], [219, 1]], ![[223, 100], [121], [90], [1], [219, 81], [1, 154], [197, 240]]]
 h' := ![![[219, 240], [15, 158], [69, 230], [239, 50], [36, 1], [4, 94], [118, 150], [0, 1]], ![[0, 1], [154, 83], [70, 11], [103, 191], [14, 240], [105, 147], [192, 91], [219, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [116, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [93, 22, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-234, 441, -66]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36, 21, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![106, -106, -11]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![106, -106, -11]] 
 ![![241, 0, 0], ![171, 1, 0], ![161, 0, 1]] where
  M :=![![![106, -106, -11], ![-561, 711, -106], ![-5406, 5269, 711]]]
  hmulB := by decide  
  f := ![![![1064035, 17407, 19057]], ![![759012, 12417, 13594]], ![![714512, 11689, 12797]]]
  g := ![![![83, -106, -11], ![-436, 711, -106], ![-4236, 5269, 711]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![1064035, 17407, 19057]] ![![106, -106, -11]]
  ![![241, 0, 0]] where
 M := ![![![241, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0)


lemma PB243I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 242 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 242 (by omega)

def PB243I4 : PrimesBelowBoundCertificateInterval O 193 242 243 where
  m := 9
  g := ![2, 3, 1, 2, 3, 2, 2, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB243I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![199, 199, 199]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![227, 227, 227]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![58081, 241]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
      exact NI227N2
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
  β := ![I197N1, I199N0, I199N1, I199N2, I223N1, I227N0, I227N1, I227N2, I229N1, I233N1, I239N1, I241N1]
  Il := ![[I197N1], [I199N0, I199N1, I199N2], [], [I223N1], [I227N0, I227N1, I227N2], [I229N1], [I233N1], [I239N1], [I241N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
