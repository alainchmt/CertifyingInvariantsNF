
import IdealArithmetic.Examples.NF3_1_702351_1.RI3_1_702351_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1435, -151, -92]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-1435, -151, -92]] 
 ![![197, 0, 0], ![0, 197, 0], ![52, 98, 1]] where
  M :=![![![-1435, -151, -92], ![-15114, -1586, -965], ![-20079, -2116, -1284]]]
  hmulB := by decide  
  f := ![![![28, -4, 1]], ![![153, 24, -29]], ![![80, 11, -14]]]
  g := ![![![17, 45, -92], ![178, 472, -965], ![237, 628, -1284]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [60, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 196], [0, 1]]
 g := ![![[22, 23], [53], [195, 23], [85], [81], [62], [59, 1]], ![[0, 174], [53], [173, 174], [85], [81], [62], [118, 196]]]
 h' := ![![[59, 196], [188, 107], [120, 168], [22, 90], [0, 171], [59, 188], [6, 72], [0, 1]], ![[0, 1], [0, 90], [182, 29], [13, 107], [42, 26], [119, 9], [117, 125], [59, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [56, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [60, 138, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2050, 863, -938]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![258, 471, -938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, -4, 1]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![28, -4, 1]] 
 ![![197, 0, 0], ![103, 1, 0], ![46, 0, 1]] where
  M :=![![![28, -4, 1], ![153, 24, -29], ![-690, 23, 32]]]
  hmulB := by decide  
  f := ![![![-1435, -151, -92]], ![![-827, -87, -53]], ![![-437, -46, -28]]]
  g := ![![![2, -4, 1], ![-5, 24, -29], ![-23, 23, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-1435, -151, -92]] ![![28, -4, 1]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5088697063, -311006601, -130127808]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![5088697063, -311006601, -130127808]] 
 ![![199, 0, 0], ![0, 199, 0], ![60, 21, 1]] where
  M :=![![![5088697063, -311006601, -130127808], ![-21572590290, 4777690462, -2046918399], ![-44086183593, -2992939584, 5399703664]]]
  hmulB := by decide  
  f := ![![![98853314530322848, 10396020856734864, 6323193572461905]], ![![1038826206879836433, 109249335387057712, 66448952424682143]], ![![146379103868829153, 15394124355270993, 9363200547435313]]]
  g := ![![![64805857, 12169233, -130127808], ![508756350, 240014959, -2046918399], ![-1849589967, -584857872, 5399703664]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [46, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 198], [0, 1]]
 g := ![![[41, 13], [19, 40], [66, 144], [184], [162], [178], [104, 1]], ![[0, 186], [0, 159], [117, 55], [184], [162], [178], [9, 198]]]
 h' := ![![[104, 198], [121, 150], [148, 144], [74, 187], [141, 69], [35, 19], [191, 24], [0, 1]], ![[0, 1], [0, 49], [0, 55], [20, 12], [153, 130], [21, 180], [100, 175], [104, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [34, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [46, 95, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14358, 7452, 1890]
  a := ![5, 0, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-642, -162, 1890]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-98853314530322848, -10396020856734864, -6323193572461905]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-98853314530322848, -10396020856734864, -6323193572461905]] 
 ![![199, 0, 0], ![53, 1, 0], ![160, 0, 1]] where
  M :=![![![-98853314530322848, -10396020856734864, -6323193572461905], ![-1038826206879836433, -109249335387057712, -66448952424682143], ![-1382892453601065474, -145433452166623815, -88457293673587984]]]
  hmulB := by decide  
  f := ![![![-5088697063, 311006601, 130127808]], ![![-1246876151, 58822409, 44943177]], ![![-3869876113, 265095456, 77491184]]]
  g := ![![![7356013881761456, -10396020856734864, -6323193572461905], ![77302617872278217, -109249335387057712, -66448952424682143], ![102905766326653639, -145433452166623815, -88457293673587984]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![5088697063, -311006601, -130127808]] ![![-98853314530322848, -10396020856734864, -6323193572461905]]
  ![![199, 0, 0]] where
 M := ![![![-199, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-108466048, 18968351, -6495510]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-108466048, 18968351, -6495510]] 
 ![![211, 0, 0], ![0, 211, 0], ![145, 53, 1]] where
  M :=![![![-108466048, 18968351, -6495510], ![-1007840408, -89497697, 139273967], ![3352697971, -149396730, -127434399]]]
  hmulB := by decide  
  f := ![![![152664267644583, 16055110726959, 9765233674777]], ![![1604312843093015, 168719378371542, 102620541413936]], ![![518012187537417, 54477338784932, 33134866041227]]]
  g := ![![![3949682, 1721471, -6495510], ![-100486093, -35407668, 139273967], ![103462966, 31301547, -127434399]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [178, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 210], [0, 1]]
 g := ![![[175, 179], [99, 201], [125], [19], [73, 58], [4], [78, 1]], ![[0, 32], [163, 10], [125], [19], [166, 153], [4], [156, 210]]]
 h' := ![![[78, 210], [102, 161], [24, 137], [142, 114], [88, 21], [208, 144], [42, 209], [0, 1]], ![[0, 1], [0, 50], [160, 74], [172, 97], [38, 190], [46, 67], [97, 2], [78, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [177, 174]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [178, 133, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2283294, 914855, 3001]
  a := ![-66, -64, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8759, 3582, 3001]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![152664267644583, 16055110726959, 9765233674777]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![152664267644583, 16055110726959, 9765233674777]] 
 ![![211, 0, 0], ![52, 1, 0], ![119, 0, 1]] where
  M :=![![![152664267644583, 16055110726959, 9765233674777], ![1604312843093015, 168719378371542, 102620541413936], ![2135672078000657, 224600374519871, 136609156917624]]]
  hmulB := by decide  
  f := ![![![-108466048, 18968351, -6495510]], ![![-31507464, 4250505, -940723]], ![![-45283231, 9989749, -4267299]]]
  g := ![![![-8740589087468, 16055110726959, 9765233674777], ![-91852792703723, 168719378371542, 102620541413936], ![-122275057204881, 224600374519871, 136609156917624]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-108466048, 18968351, -6495510]] ![![152664267644583, 16055110726959, 9765233674777]]
  ![![211, 0, 0]] where
 M := ![![![211, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![832889517, 87591770, 53276126]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![832889517, 87591770, 53276126]] 
 ![![223, 0, 0], ![0, 223, 0], ![80, 36, 1]] where
  M :=![![![832889517, 87591770, 53276126], ![8752639826, 920481287, 559866264], ![11651573174, 1225350898, 745297747]]]
  hmulB := by decide  
  f := ![![![19979, -3054, 866]], ![![133318, 16925, -22244]], ![![26306, 1726, -3177]]]
  g := ![![![-15377581, -8207842, 53276126], ![-161599378, -86254279, 559866264], ![-215122182, -114822278, 745297747]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [50, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [141, 222], [0, 1]]
 g := ![![[73, 58], [221, 181], [185, 220], [51, 82], [181, 86], [33], [141, 1]], ![[0, 165], [97, 42], [208, 3], [17, 141], [42, 137], [33], [59, 222]]]
 h' := ![![[141, 222], [100, 110], [116, 187], [126, 144], [93, 64], [171, 117], [86, 207], [0, 1]], ![[0, 1], [0, 113], [169, 36], [137, 79], [197, 159], [166, 106], [60, 16], [141, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [202, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [50, 82, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9441, 7381, -1325]
  a := ![-5, -1, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![433, 247, -1325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19979, 3054, -866]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-19979, 3054, -866]] 
 ![![223, 0, 0], ![195, 1, 0], ![179, 0, 1]] where
  M :=![![![-19979, 3054, -866], ![-133318, -16925, 22244], ![531530, -19918, -23033]]]
  hmulB := by decide  
  f := ![![![-832889517, -87591770, -53276126]], ![![-767560967, -80721419, -49097358]], ![![-720801779, -75803936, -46106387]]]
  g := ![![![-2065, 3054, -866], ![-3653, -16925, 22244], ![38289, -19918, -23033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![832889517, 87591770, 53276126]] ![![-19979, 3054, -866]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-286550521, 190167722, -122370141]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-286550521, 190167722, -122370141]] 
 ![![227, 0, 0], ![123, 1, 0], ![59, 0, 1]] where
  M :=![![![-286550521, 190167722, -122370141], ![-19321257257, -96382799, 1453544195], ![36246029728, -2814513243, -476718243]]]
  hmulB := by decide  
  f := ![![![-4136966824707976542, -435068804699429709, -264622811685869131]], ![![-2433133611144955525, -255883253777256654, -155636408187542035]], ![![-1330195906946382463, -139891560114719572, -85086537046144606]]]
  g := ![![![-72499304, 190167722, -122370141], ![-410684055, -96382799, 1453544195], ![1808623502, -2814513243, -476718243]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N0 : Nat.card (O ⧸ I227N0) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N0)

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := prime_ideal_of_norm_prime hp227.out _ NI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-412728391, -43405049, -26400344]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-412728391, -43405049, -26400344]] 
 ![![227, 0, 0], ![163, 1, 0], ![8, 0, 1]] where
  M :=![![![-412728391, -43405049, -26400344], ![-4337265482, -456133440, -277434999], ![-5773797065, -607207912, -369323342]]]
  hmulB := by decide  
  f := ![![![-244392, 32030, -6591]], ![![-179881, 22064, -3716]], ![![15440, 461, -1450]]]
  g := ![![![30279724, -43405049, -26400344], ![318202490, -456133440, -277434999], ![423593301, -607207912, -369323342]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3341153581, -351376203, -213718285]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![-3341153581, -351376203, -213718285]] 
 ![![227, 0, 0], ![168, 1, 0], ![160, 0, 1]] where
  M :=![![![-3341153581, -351376203, -213718285], ![-35111396291, -3692529784, -2245915136], ![-46740527573, -4915520555, -2989777378]]]
  hmulB := by decide  
  f := ![![![-805872, 87559, -8168]], ![![-601438, 61637, -3309]], ![![-504259, 60888, -9693]]]
  g := ![![![395969049, -351376203, -213718285], ![4161145503, -3692529784, -2245915136], ![5539344961, -4915520555, -2989777378]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-286550521, 190167722, -122370141]] ![![-412728391, -43405049, -26400344]]
  ![![805872, -87559, 8168]] where
 M := ![![![805872, -87559, 8168]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![805872, -87559, 8168]] ![![-3341153581, -351376203, -213718285]]
  ![![227, 0, 0]] where
 M := ![![![-227, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-313, 521, -369]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-313, 521, -369]] 
 ![![229, 0, 0], ![0, 229, 0], ![138, 11, 1]] where
  M :=![![![-313, 521, -369], ![-58367, 208, 4016], ![100855, -8487, -834]]]
  hmulB := by decide  
  f := ![![![148080, 15573, 9472]], ![![1556138, 163653, 99539]], ![![173031, 18197, 11068]]]
  g := ![![![221, 20, -369], ![-2675, -192, 4016], ![943, 3, -834]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [78, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [121, 228], [0, 1]]
 g := ![![[19, 138], [57], [180, 56], [196], [44], [182, 176], [121, 1]], ![[0, 91], [57], [86, 173], [196], [44], [181, 53], [13, 228]]]
 h' := ![![[121, 228], [137, 67], [158, 61], [104, 96], [7, 14], [2, 161], [180, 136], [0, 1]], ![[0, 1], [0, 162], [211, 168], [41, 133], [98, 215], [18, 68], [148, 93], [121, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [201]]
 b := ![[], [160, 215]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [78, 108, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2128, 923, -728]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![448, 39, -728]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![148080, 15573, 9472]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![148080, 15573, 9472]] 
 ![![229, 0, 0], ![153, 1, 0], ![102, 0, 1]] where
  M :=![![![148080, 15573, 9472], ![1556138, 163653, 99539], ![2071541, 217856, 132507]]]
  hmulB := by decide  
  f := ![![![-313, 521, -369]], ![![-464, 349, -229]], ![![301, 195, -168]]]
  g := ![![![-13977, 15573, 9472], ![-146881, 163653, 99539], ![-195529, 217856, 132507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-313, 521, -369]] ![![148080, 15573, 9472]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [48, 170, 224, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 55, 227], [223, 177, 6], [0, 1]]
 g := ![![[53, 205, 46], [176, 14], [63, 36], [104, 230, 220], [99, 170], [44, 232, 81], [1]], ![[222, 147, 33, 20], [152, 200], [142, 232], [75, 211, 0, 122], [140, 23], [220, 142, 29, 145], [32, 15, 35, 17]], ![[89, 174, 225, 168], [71, 210], [189, 132], [218, 171, 185, 5], [110, 224], [186, 64, 95, 149], [56, 119, 90, 216]]]
 h' := ![![[19, 55, 227], [107, 172, 38], [20, 140, 125], [134, 153, 6], [133, 1, 57], [218, 231, 183], [185, 63, 9], [0, 1]], ![[223, 177, 6], [158, 81, 102], [124, 7, 82], [154, 79, 144], [103, 83, 64], [84, 78, 16], [197, 48, 50], [19, 55, 227]], ![[0, 1], [150, 213, 93], [23, 86, 26], [170, 1, 83], [88, 149, 112], [3, 157, 34], [40, 122, 174], [223, 177, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162, 194], []]
 b := ![[], [20, 27, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [48, 170, 224, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27210206, 2683927, 1595351]
  a := ![3, 21, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![116782, 11519, 6847]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀



lemma PB238I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 237 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 237 (by omega)

def PB238I4 : PrimesBelowBoundCertificateInterval O 193 237 238 where
  m := 7
  g := ![2, 2, 2, 2, 3, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233]
  hP := PB238I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![227, 227, 227]
    · exact ![52441, 229]
    · exact ![12649337]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
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
  β := ![I197N1, I199N1, I211N1, I223N1, I227N0, I227N1, I227N2, I229N1]
  Il := ![[I197N1], [I199N1], [I211N1], [I223N1], [I227N0, I227N1, I227N2], [I229N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
