
import IdealArithmetic.Examples.NF3_1_975819_1.RI3_1_975819_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-27, 3, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-27, 3, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-27, 3, 1], ![-302, 18, 14], ![-726, 50, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![14, -1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -1, 2]], ![![-14, 1, 1], ![-158, 2, 14], ![-368, 20, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2029, -6855, 5601]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1786, -6228, 5601]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-2, 2, 5], ![-296, 39, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, 0, -2], ![-2, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-1, 2, 5], ![-148, 39, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-27, 3, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![-54, 6, 2], ![-302, 18, 14]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![-27, 3, 1]], ![![-151, 9, 7]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 1, 0]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![-2, 2, 5], ![-296, 39, -1]]]
  hmulB := by decide  
  f := ![![![-3, 3, 10], ![3, -6, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, 2, 7], ![2, -4, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-2, 0, 3]], ![![0, 1, 0], ![-4, 2, 5], ![-98, 39, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6527525, 1137609, -369350]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-6527525, 1137609, -369350]] 
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![-6527525, 1137609, -369350], ![107052382, -18656957, 6057395], ![-396566964, 69113201, -22439134]]]
  hmulB := by decide  
  f := ![![![16157, -1256, -605]], ![![71302, -4154, -2295]], ![![96641, -3235, -2464]]]
  g := ![![![-2811131, 1137609, -369350], ![46102967, -18656957, 6057395], ![-170784744, 69113201, -22439134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![16157, -1256, -605]] where
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![-2, 2, 5]]]
 hmul := by decide  
 g := ![![![![-19582575, 3412827, -1108050]], ![![107052382, -18656957, 6057395]]], ![![![107052382, -18656957, 6057395]], ![![-585225002, 101992291, -33114060]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![16157, -1256, -605]] ![![-6527525, 1137609, -369350]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-26, 2, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-26, 2, 1]] 
 ![![5, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-26, 2, 1], ![-300, 17, 9], ![-430, 11, 12]]]
  hmulB := by decide  
  f := ![![![85, 30, 12], ![-330, 30, 0]], ![![27, 3, 1], ![-41, 4, 0]], ![![34, 12, 5], ![-132, 12, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-2, 0, 5]], ![![-6, 2, 1], ![-67, 17, 9], ![-93, 11, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![52, -2, -2]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![52, -2, -2]] 
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![52, -2, -2], ![596, -30, -8], ![268, 56, -26]]]
  hmulB := by decide  
  f := ![![![-7, -28, 60], ![230, -20, 0]], ![![-27, -3, 10], ![37, -3, 0]], ![![-25, -16, 37], ![140, -12, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-3, 0, 5]], ![![12, -2, -2], ![130, -30, -8], ![58, 56, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5185693762838487, 191039919173626, -33786140774680]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![5185693762838487, 191039919173626, -33786140774680]] 
 ![![5, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![5185693762838487, 191039919173626, -33786140774680], ![9618617830958028, 4250114110973219, 988985736642810], ![-62021170880891456, 9714228279674974, 3643208212677661]]]
  hmulB := by decide  
  f := ![![![5876817422824076268801916523819, -1024204486657106989442799427106, 332530708853906504716127823980]], ![![-16925409200358791775896880799246, 2949739424299600398991940790123, -957698344886325688499573862310]], ![![72582264061532119781576650886391, -12649547391899203078738508258180, 4106956194498269990321191346821]]]
  g := ![![![967480013053183, 191039919173626, -33786140774680], ![25880774473756, 4250114110973219, 988985736642810], ![-17018567130583813, 9714228279674974, 3643208212677661]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-26, 2, 1]] ![![5, 0, 0], ![52, -2, -2]]
  ![![5876817422824076268801916523819, -1024204486657106989442799427106, 332530708853906504716127823980]] where
 M := ![![![25, 0, 0], ![260, -10, -10]], ![![-130, 10, 5], ![108, 48, 10]]]
 hmul := by decide  
 g := ![![![![25928468814192435, 955199595868130, -168930703873400]], ![![374461181767468180, -17994608984267834, -11021267218924302]]], ![![![-177611973052776062, 13247418603107136, 6499619346104961]], ![![80307374692725476, 64356014278843172, 16050898856393210]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5876817422824076268801916523819, -1024204486657106989442799427106, 332530708853906504716127823980]] ![![5185693762838487, 191039919173626, -33786140774680]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [3, 0, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2], [0, 4], [0, 1]]
 g := ![![[], [1]], ![[], [1]], ![[], [1]]]
 h' := ![![[0, 2], [4], [0, 1]], ![[0, 4], [4], [0, 2]], ![[0, 1], [4], [0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [0, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [3, 0, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-673589, 330743, -164815]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96227, 47249, -23545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 92, 21]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![233, 92, 21]] 
 ![![11, 0, 0], ![0, 11, 0], ![9, 7, 1]] where
  M :=![![![233, 92, 21], ![-6400, 1236, 439], ![-23830, 2181, 981]]]
  hmulB := by decide  
  f := ![![![23187, -4041, 1312]], ![![-380270, 66273, -21517]], ![![-94957, 16549, -5373]]]
  g := ![![![4, -5, 21], ![-941, -167, 439], ![-2969, -426, 981]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10], [0, 1]]
 g := ![![[2, 9], [0, 1], [1]], ![[4, 2], [10, 10], [1]]]
 h' := ![![[10, 10], [0, 8], [5, 10], [0, 1]], ![[0, 1], [3, 3], [6, 1], [10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [6, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13432, -2785, 3955]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4457, -2770, 3955]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23187, -4041, 1312]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![23187, -4041, 1312]] 
 ![![11, 0, 0], ![10, 1, 0], ![2, 0, 1]] where
  M :=![![![23187, -4041, 1312], ![-380270, 66273, -21517], ![1408680, -245503, 79708]]]
  hmulB := by decide  
  f := ![![![233, 92, 21]], ![![-370, 196, 59]], ![![-2124, 215, 93]]]
  g := ![![![5543, -4041, 1312], ![-90906, 66273, -21517], ![336754, -245503, 79708]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![233, 92, 21]] ![![23187, -4041, 1312]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1951523610956496325, 150477869712833832, 72743410744520367]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-1951523610956496325, 150477869712833832, 72743410744520367]] 
 ![![13, 0, 0], ![0, 1, 0], ![10, 0, 1]] where
  M :=![![![-1951523610956496325, 150477869712833832, 72743410744520367], ![-21833005319803696296, 1186425147505465652, 679645937819648793], ![-32757016894386514818, 994828398917654859, 807734949111484523]]]
  hmulB := by decide  
  f := ![![![-282185975992903598381687031536168809, 49179023592119905152062006336768883, -15967061059463623555124349275430492]], ![![355991694339768674000975644065683682, -62041793086749623594416356969570787, 20143244540004857639648798535328839]], ![![-1535808818063818071135182213358847474, 267658865153687548511105362458116787, -86901388658323437022305115511112484]]]
  g := ![![![-206073670646284615, 150477869712833832, 72743410744520367], ![-2202266515230783402, 1186425147505465652, 679645937819648793], ![-3141105106577027696, 994828398917654859, 807734949111484523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8312715159, -1612382369, -572087062]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![8312715159, -1612382369, -572087062]] 
 ![![13, 0, 0], ![12, 1, 0], ![5, 0, 1]] where
  M :=![![![8312715159, -1612382369, -572087062], ![172562535090, -17223444997, -7489824783], ![384587077180, -24553079237, -12958384952]]]
  hmulB := by decide  
  f := ![![![-39289769102479154573, 6847372463571179594, -2223151381156122113]], ![![13298525743486148568, -2317650652120877128, 752476701933734979]], ![![-198724739882827439615, 34633502379584006439, -11244534901390448404]]]
  g := ![![![2347826069, -1612382369, -572087062], ![32053307613, -17223444997, -7489824783], ![57231996368, -24553079237, -12958384952]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-1951523610956496325, 150477869712833832, 72743410744520367]] ![![-1951523610956496325, 150477869712833832, 72743410744520367]]
  ![![-1859796860545897325901673454851678853, -42763176057893022774861987582115683, 19068584448564870703264187063993442]] where
 M := ![![![-1859796860545897325901673454851678853, -42763176057893022774861987582115683, 19068584448564870703264187063993442]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-1859796860545897325901673454851678853, -42763176057893022774861987582115683, 19068584448564870703264187063993442]] ![![8312715159, -1612382369, -572087062]]
  ![![13, 0, 0]] where
 M := ![![![-15505752465336936660940710385349431224591795537, 3267040413692865107729103564058209608594566954, 1137156359930501283553685312736089211047186891]]]
 hmul := by decide  
 g := ![![![![-1192750189641302820072362337334571632660907349, 251310801053297315979161812619862277584197458, 87473566148500098734898870210468400849783607]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [15, 15, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 1, 12], [1, 15, 5], [0, 1]]
 g := ![![[13, 15, 13], [], [10, 1], []], ![[1, 3, 0, 5], [16, 13], [7, 4], [2, 8]], ![[9, 10, 0, 6], [4, 13], [2, 1], [9, 8]]]
 h' := ![![[9, 1, 12], [9, 13, 8], [3, 5], [0, 0, 1], [0, 1]], ![[1, 15, 5], [7, 11, 4], [14, 5, 9], [0, 4, 15], [9, 1, 12]], ![[0, 1], [4, 10, 5], [8, 7, 8], [2, 13, 1], [1, 15, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 10], []]
 b := ![[], [14, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [15, 15, 7, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10440210, 8032925, -4328625]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-614130, 472525, -254625]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-358720010591275031687027122330333058237025025, 62517280675484258515641182424026108386213764, -20297622134511625229656155635986731618124686]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-358720010591275031687027122330333058237025025, 62517280675484258515641182424026108386213764, -20297622134511625229656155635986731618124686]] 
 ![![19, 0, 0], ![0, 1, 0], ![11, 0, 1]] where
  M :=![![![-358720010591275031687027122330333058237025025, 62517280675484258515641182424026108386213764, -20297622134511625229656155635986731618124686], ![5883061590464472550946939703404020342192479528, -1025292712486259898612334827285763374571460251, 332884025511932917807862067756117273549193506], ![-21793329865734223807834087210541578604455473276, 3798114629356164972496968542148129245476690758, -1233142176647224299388914530193828431348226229]]]
  hmulB := by decide  
  f := ![![![213505524211097434694069, -23629401572285517763968, -9893023692577905760398]], ![![156610200849875323189776, -11556905418105890815231, -5697578114149983318918]], ![![407378620711629700346569, -27296710063766115907986, -14074172765162644280119]]]
  g := ![![![-7128745637455113376884705807077842654613341, 62517280675484258515641182424026108386213764, -20297622134511625229656155635986731618124686], ![116912489991221602897918787267722649113228998, -1025292712486259898612334827285763374571460251, 332884025511932917807862067756117273549193506], ![-433092943295513500766106704126813992611841303, 3798114629356164972496968542148129245476690758, -1233142176647224299388914530193828431348226229]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-213505524211097434694069, 23629401572285517763968, 9893023692577905760398]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-213505524211097434694069, 23629401572285517763968, 9893023692577905760398]] 
 ![![19, 0, 0], ![0, 19, 0], ![10, 4, 1]] where
  M :=![![![-213505524211097434694069, 23629401572285517763968, 9893023692577905760398], ![-2975593816147631140605744, 219581202944011925489389, 108253984168849683059442], ![-5391633027198892524950052, 258714073916415506848086, 158586021919733277957883]]]
  hmulB := by decide  
  f := ![![![358720010591275031687027122330333058237025025, -62517280675484258515641182424026108386213764, 20297622134511625229656155635986731618124686]], ![![-5883061590464472550946939703404020342192479528, 1025292712486259898612334827285763374571460251, -332884025511932917807862067756117273549193506]], ![![97278084725741258995610506327833043055568706, -16953504535050945431791634591859833213315126, 5504331365505730550211990291011929122773635]]]
  g := ![![![-16443987428256657489371, -839089115685584488296, 9893023692577905760398], ![-213585981991375156378956, -11233407038494042460441, 108253984168849683059442], ![-367236486652432910764678, -19770000724343031841234, 158586021919733277957883]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [12, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 18], [0, 1]]
 g := ![![[11, 16], [5, 16], [1], [1]], ![[8, 3], [2, 3], [1], [1]]]
 h' := ![![[1, 18], [16, 4], [18, 15], [7, 1], [0, 1]], ![[0, 1], [1, 15], [14, 4], [8, 18], [1, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [2, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [12, 18, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60348, -19652, 10420]
  a := ![-6, -2, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2308, -3228, 10420]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-358720010591275031687027122330333058237025025, 62517280675484258515641182424026108386213764, -20297622134511625229656155635986731618124686]] ![![-213505524211097434694069, 23629401572285517763968, 9893023692577905760398]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [19, 18, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 18, 15], [17, 4, 8], [0, 1]]
 g := ![![[15, 3, 16], [0, 19, 4], [0, 8, 1], []], ![[16, 10, 1, 20], [4, 6, 11, 21], [5, 18, 16, 10], [17, 18]], ![[3, 20, 8, 1], [8, 10, 16, 18], [9, 6, 1, 16], [1, 18]]]
 h' := ![![[14, 18, 15], [0, 7, 19], [0, 9, 21], [0, 0, 1], [0, 1]], ![[17, 4, 8], [8, 12, 20], [12, 13, 12], [11, 17, 4], [14, 18, 15]], ![[0, 1], [5, 4, 7], [4, 1, 13], [17, 6, 18], [17, 4, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 14], []]
 b := ![[], [17, 0, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [19, 18, 15, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![409174853, -221633888, 113604061]
  a := ![-15, 27, 44]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17790211, -9636256, 4939307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1502992552127998131684201352855307416019, 261939686831716100908831890076434532228, -85044530534537688883931378527212769578]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-1502992552127998131684201352855307416019, 261939686831716100908831890076434532228, -85044530534537688883931378527212769578]] 
 ![![29, 0, 0], ![0, 29, 0], ![16, 27, 1]] where
  M :=![![![-1502992552127998131684201352855307416019, 261939686831716100908831890076434532228, -85044530534537688883931378527212769578], ![24649301664559723707826024263902110730632, -4295849869311535796339861335263736365105, 1394742964693118193428090828909385430718], ![-91311361248783071468211122784033090211124, 15913631332250953090667846074304202318618, -5166713460341221787950288384020252731367]]]
  hmulB := by decide  
  f := ![![![-159962884184013697959, 10142691595482255432, 5370999639759055034]], ![![-1610101276559644800928, 69791484957553959231, 45342458337652222126]], ![![-1660837082230221016716, 71805557094538767611, 46721268247021418135]]]
  g := ![![![-4906209088806727915217217117927693199, 88211793491870127612930314148661355546, -85044530534537688883931378527212769578], ![80462559636890779757812793150067028936, -1446686548828473345479252197097142861879, 1394742964693118193428090828909385430718], ![-298067099424949064172638228955484362388, 5359134302119446253976745946305207795363, -5166713460341221787950288384020252731367]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [8, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 28], [0, 1]]
 g := ![![[11, 9], [20], [13, 20], [28, 1]], ![[2, 20], [20], [22, 9], [27, 28]]]
 h' := ![![[28, 28], [13, 3], [12, 7], [8, 22], [0, 1]], ![[0, 1], [10, 26], [5, 22], [15, 7], [28, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [15, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [8, 1, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4110, 376, 218]
  a := ![1, -4, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-262, -190, 218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![159962884184013697959, -10142691595482255432, -5370999639759055034]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![159962884184013697959, -10142691595482255432, -5370999639759055034]] 
 ![![29, 0, 0], ![11, 1, 0], ![0, 0, 1]] where
  M :=![![![159962884184013697959, -10142691595482255432, -5370999639759055034], ![1610101276559644800928, -69791484957553959231, -45342458337652222126], ![2132134770621780692364, -35707996359951274570, -44734409810866247969]]]
  hmulB := by decide  
  f := ![![![1502992552127998131684201352855307416019, -261939686831716100908831890076434532228, 85044530534537688883931378527212769578]], ![![-279875296246611871010338254568749281187, 48776321178022713322162432566308845193, -15836314786662193644994678107242929840]], ![![3148667629268381774765900785656313455556, -548745908008653554850615381872558700642, 178162533115214544412078909793801818323]]]
  g := ![![![9363189370148914059, -10142691595482255432, -5370999639759055034], ![81993365899749598361, -69791484957553959231, -45342458337652222126], ![87066301054525679746, -35707996359951274570, -44734409810866247969]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-1502992552127998131684201352855307416019, 261939686831716100908831890076434532228, -85044530534537688883931378527212769578]] ![![159962884184013697959, -10142691595482255432, -5370999639759055034]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2376012910365045075, -20212304201625128, 33653101677726650]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-2376012910365045075, -20212304201625128, 33653101677726650]] 
 ![![31, 0, 0], ![0, 31, 0], ![30, 6, 1]] where
  M :=![![![-2376012910365045075, -20212304201625128, 33653101677726650], ![-9920893488203838144, -1103966553336955981, -134714622685852290], ![11434644515472755188, -3043037676271065542, -1009676539054353947]]]
  hmulB := by decide  
  f := ![![![-22732498594430072011830169381026317, 3961791796171414133913370491331436, -1286283600077148922365529385836670]], ![![372816362030493252752369957224991448, -64973975405096051716259074445993575, 21095242580934219591932381842493850]], ![![5608222563574859583798104386435922, -977394106115476040614239158807596, 317332680309787317427861102388337]]]
  g := ![![![-109213095506349825, -7165513363483388, 33653101677726650], ![-189659832504137724, -9538026361994911, -134714622685852290], ![1345965828616237858, 97258759937259940, -1009676539054353947]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [24, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 30], [0, 1]]
 g := ![![[26, 8], [5, 1], [6, 2], [27, 1]], ![[25, 23], [1, 30], [29, 29], [23, 30]]]
 h' := ![![[27, 30], [4, 15], [11, 30], [3, 23], [0, 1]], ![[0, 1], [6, 16], [15, 1], [4, 8], [27, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [14, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [24, 4, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26293, -5488, 7693]
  a := ![5, -7, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8293, -1666, 7693]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22732498594430072011830169381026317, 3961791796171414133913370491331436, -1286283600077148922365529385836670]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-22732498594430072011830169381026317, 3961791796171414133913370491331436, -1286283600077148922365529385836670]] 
 ![![31, 0, 0], ![2, 1, 0], ![29, 0, 1]] where
  M :=![![![-22732498594430072011830169381026317, 3961791796171414133913370491331436, -1286283600077148922365529385836670], ![372816362030493252752369957224991448, -64973975405096051716259074445993575, 21095242580934219591932381842493850], ![-1381068314879236709061573425939645596, 240690881255854129021111918012982894, -78145634393687443040364715305824553]]]
  hmulB := by decide  
  f := ![![![-2376012910365045075, -20212304201625128, 33653101677726650]], ![![-473319977707546074, -36915843927103427, -2174465139690290]], ![![-1853862254358501677, -117070790261877234, -1088277109686487]]]
  g := ![![![214391684369819950611078768566911, 3961791796171414133913370491331436, -1286283600077148922365529385836670], ![-3516055548593774580037127977914292, -64973975405096051716259074445993575, 21095242580934219591932381842493850], ![13024945807290028421509015545267763, 240690881255854129021111918012982894, -78145634393687443040364715305824553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-2376012910365045075, -20212304201625128, 33653101677726650]] ![![-22732498594430072011830169381026317, 3961791796171414133913370491331436, -1286283600077148922365529385836670]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB280I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB280I0 : PrimesBelowBoundCertificateInterval O 1 31 280 where
  m := 11
  g := ![2, 3, 3, 1, 2, 3, 1, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB280I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
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
    · exact ![4, 2]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![343]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![19, 361]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N0
      exact NI13N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I5N2, I11N0, I11N1, I13N0, I13N1, I19N0, I29N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N1], [I5N0, I5N1, I5N2], [], [I11N0, I11N1], [I13N0, I13N0, I13N1], [], [I19N0], [], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
