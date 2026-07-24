
import IdealArithmetic.Examples.NF3_1_720575_1.RI3_1_720575_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-13, 1, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-13, 1, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-13, 1, 1], ![-176, 7, 2], ![-88, -69, 6]]]
  hmulB := by decide  
  f := ![![![8, 6, 11], ![-26, 2, 0]], ![![3, -3, -6], ![14, -1, 0]], ![![4, 3, 6], ![-13, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![-7, 1, 1], ![-89, 7, 2], ![-47, -69, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-12, 2, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-12, 2, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-12, 2, 1], ![-176, 9, 4], ![-264, -50, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-4, -9, -5], ![14, -1, 0]], ![![6, -1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-6, 2, 1], ![-88, 9, 4], ![-132, -50, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37529, 63929, 14484]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-37529, 63929, 14484]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-37529, 63929, 14484], ![-2549184, 301596, 127858], ![-9976912, -59941, 237667]]]
  hmulB := by decide  
  f := ![![![79343352910, -16061999087, 3805517618]], ![![-295213873929, 59762094739, -14159240278]], ![![1620570371303, -328062766062, 77726852635]]]
  g := ![![![-57971, 63929, 14484], ![-1489319, 301596, 127858], ![-5077319, -59941, 237667]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-13, 1, 1]] ![![2, 0, 0], ![-12, 2, 1]]
  ![![79343352910, -16061999087, 3805517618]] where
 M := ![![![4, 0, 0], ![-24, 4, 2]], ![![-26, 2, 2], ![-284, -67, -2]]]
 hmul := by decide  
 g := ![![![![-75058, 127858, 28968]], ![![-14624932, -223897, 319575]]], ![![![-12038219, -589422, 177233]], ![![100703694, -19121443, -6577638]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![79343352910, -16061999087, 3805517618]] ![![-37529, 63929, 14484]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 1], [2, 0, 2], [0, 1]]
 g := ![![[1]], ![[0, 0, 1, 1]], ![[2, 0, 2, 2]]]
 h' := ![![[2, 2, 1], [0, 1]], ![[2, 0, 2], [2, 2, 1]], ![[0, 1], [2, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [0, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 1, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-282567, 75012, -3648]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-94189, 25004, -1216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2382006532685671, -17946601611734, -63576654446118]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![2382006532685671, -17946601611734, -63576654446118]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![2382006532685671, -17946601611734, -63576654446118], ![11189491182516768, 1156103496597695, -35893203223468], ![-2436143707593200, 5253760160635438, 1174050098209429]]]
  hmulB := by decide  
  f := ![![![1545897704853835741217862725139, -312946284890718837727936489798, 74145353525960998720673471522]], ![![-1682377821201525710236988562491, 340574856456843873199782544973, -80691301840710935858770513006]], ![![13557385614093285258481507719788, -2744511132554220231032360951858, 650248167190187742358670514029]]]
  g := ![![![538030591061069, -17946601611734, -63576654446118], ![1572950701123511, 1156103496597695, -35893203223468], ![-4578724916467446, 5253760160635438, 1174050098209429]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![2382006532685671, -17946601611734, -63576654446118]] ![![2382006532685671, -17946601611734, -63576654446118]]
  ![![5628023647945311423621671362129, -397513545429529723399408946328, -225438022594423768244087248288]] where
 M := ![![![5628023647945311423621671362129, -397513545429529723399408946328, -225438022594423768244087248288]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5628023647945311423621671362129, -397513545429529723399408946328, -225438022594423768244087248288]] ![![2382006532685671, -17946601611734, -63576654446118]]
  ![![5, 0, 0]] where
 M := ![![![9507214204196130381624308994642127688398767255, -1744967999886133703545343895582730994390765790, -608218412776938838543781382288518474639947270]]]
 hmul := by decide  
 g := ![![![![1901442840839226076324861798928425537679753451, -348993599977226740709068779116546198878153158, -121643682555387767708756276457703694927989454]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-11, 1, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-11, 1, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![3, 1, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-11, 1, 1], ![-176, 9, 2], ![-88, -69, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -1, 7]], ![![-2, 0, 1], ![-26, 1, 2], ![-16, -11, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[1, 4], [5, 1]], ![[0, 3], [3, 6]]]
 h' := ![![[5, 6], [4, 2], [0, 1]], ![[0, 1], [0, 5], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1, -1255, 306]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-131, -223, 306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-2, 1, 0]] 
 ![![7, 0, 0], ![5, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-2, 1, 0], ![0, -1, 2], ![-176, 19, -2]]]
  hmulB := by decide  
  f := ![![![3, 2, -6], ![7, 21, 0]], ![![1, 2, -4], ![1, 14, 0]], ![![2, 2, -5], ![4, 18, 0]]]
  g := ![![![1, 0, 0], ![-5, 7, 0], ![-6, 0, 7]], ![![-1, 1, 0], ![-1, -1, 2], ![-37, 19, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-11, 1, 1]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-14, 7, 0]], ![![-77, 7, 7], ![-154, 7, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-2, 1, 0]]], ![![![-11, 1, 1]], ![![-22, 1, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![0, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![0, 1, 0]] 
 ![![11, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![0, 1, 2], ![-176, 19, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![5, 6, 0]]]
  g := ![![![1, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![0, 1, 2], ![-16, 19, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-8, 0, 1]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-8, 0, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![3, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-8, 0, 1], ![-176, 11, 0], ![88, -88, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, 0, 11]], ![![-1, 0, 1], ![-16, 1, 0], ![5, -8, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 3, 1] where
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

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [6, 3, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1310, -1826, 458]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-244, -166, 458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![-8, 0, 1]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-88, 0, 11]], ![![0, 11, 0], ![-176, 11, 0]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-8, 0, 1]]], ![![![0, 1, 0]], ![![-16, 1, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-16, -1, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-16, -1, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![10, 12, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-16, -1, 1], ![-176, 2, -2], ![264, -107, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -12, 13]], ![![-2, -1, 1], ![-12, 2, -2], ![18, -11, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[7, 1], [3], [6, 1]], ![[0, 12], [3], [12, 12]]]
 h' := ![![[6, 12], [7, 1], [7, 9], [0, 1]], ![[0, 1], [0, 12], [9, 4], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [1, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1319, -574, 158]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-223, -190, 158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![2, 1, 0]] 
 ![![13, 0, 0], ![2, 1, 0], ![10, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![2, 1, 0], ![0, 3, 2], ![-176, 19, 2]]]
  hmulB := by decide  
  f := ![![![7, 3, 0], ![-39, 0, 0]], ![![-2, -1, 0], ![14, 0, 0]], ![![6, 1, -1], ![-34, 7, 0]]]
  g := ![![![1, 0, 0], ![-2, 13, 0], ![-10, 0, 13]], ![![0, 1, 0], ![-2, 3, 2], ![-18, 19, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-16, -1, 1]] ![![13, 0, 0], ![2, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![26, 13, 0]], ![![-208, -13, 13], ![-208, 0, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![2, 1, 0]]], ![![![-16, -1, 1]], ![![-16, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [16, 6, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 3, 16], [4, 13, 1], [0, 1]]
 g := ![![[1], [6, 4], [5, 1], []], ![[0, 13, 4, 16], [0, 16], [10, 16], [16, 1]], ![[13, 13, 10, 1], [1, 2], [1, 9], [14, 1]]]
 h' := ![![[1, 3, 16], [14, 1], [5, 5, 2], [0, 0, 1], [0, 1]], ![[4, 13, 1], [15, 3, 16], [10, 7, 4], [0, 13, 13], [1, 3, 16]], ![[0, 1], [1, 13, 1], [0, 5, 11], [13, 4, 3], [4, 13, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 12], []]
 b := ![[], [8, 5, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [16, 6, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![65985075, -25397184, 613207]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3881475, -1493952, 36071]
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


def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12893611524838336901, 1455859740840754736, 631955468493360158]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-12893611524838336901, 1455859740840754736, 631955468493360158]] 
 ![![19, 0, 0], ![12, 1, 0], ![17, 0, 1]] where
  M :=![![![-12893611524838336901, 1455859740840754736, 631955468493360158], ![-111224162454831387808, 569402117376260837, 2911719481681509472], ![-200619233160557139632, -27950746151441353920, -886457623464493899]]]
  hmulB := by decide  
  f := ![![![80879981248921253701760579171765196777, -16373068912909774796339428624277763696, 3879218388154192918909958304221327146]], ![![15148280982732478457524962553590988612, -3066566591788218589019093955981079763, 726551728001619233381086442215810440]], ![![241999527792702665997355032345493239187, -48989563106437940501699776907656646416, 11606939116972220988553635690722788107]]]
  g := ![![![-2163535335753395601, 1455859740840754736, 631955468493360158], ![-8818748371154325204, 569402117376260837, 2911719481681509472], ![7887342118717658089, -27950746151441353920, -886457623464493899]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18046137, -20188030, -3823622]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-18046137, -20188030, -3823622]] 
 ![![19, 0, 0], ![13, 1, 0], ![4, 0, 1]] where
  M :=![![![-18046137, -20188030, -3823622], ![672957472, -110882985, -40376060], ![3216614544, -47093834, -90694955]]]
  hmulB := by decide  
  f := ![![![-8155063867626635, 1650883452641902, -391138489690130]], ![![-1956602952299125, 396088061328817, -93843866351994]], ![![-18820838433063828, 3810026658078694, -902697322657875]]]
  g := ![![![13668039, -20188030, -3823622], ![119786343, -110882985, -40376060], ![220611274, -47093834, -90694955]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-12893611524838336901, 1455859740840754736, 631955468493360158]] ![![-12893611524838336901, 1455859740840754736, 631955468493360158]]
  ![![-122463983654035386994181239846321956743, -35605947192888033773734990408905358464, -4469334884484794849355772823122407008]] where
 M := ![![![-122463983654035386994181239846321956743, -35605947192888033773734990408905358464, -4469334884484794849355772823122407008]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-122463983654035386994181239846321956743, -35605947192888033773734990408905358464, -4469334884484794849355772823122407008]] ![![-18046137, -20188030, -3823622]]
  ![![19, 0, 0]] where
 M := ![![![-36127413975945295450172374179640085215915315569, 6630878399567308073472306803214377778684910002, 2311229968552367586466369252696370203631799626]]]
 hmul := by decide  
 g := ![![![![-1901442840839226076324861798928425537679753451, 348993599977226740709068779116546198878153158, 121643682555387767708756276457703694927989454]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91471222151776121, 18517123776646336, -4387202389006980]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-91471222151776121, 18517123776646336, -4387202389006980]] 
 ![![23, 0, 0], ![0, 23, 0], ![13, 18, 1]] where
  M :=![![![-91471222151776121, 18517123776646336, -4387202389006980], ![772147620465228480, -156310943766262405, 37034247553292672], ![-3645087594922369376, 737899161988894624, -174828067542908741]]]
  hmulB := by decide  
  f := ![![![576748401, -11284672, -16863604]], ![![2967994304, 245055253, -22569344]], ![![2670597035, 240603574, -16049353]]]
  g := ![![![-1497286569334147, 4238555077337912, -4387202389006980], ![12639234881409728, -35779452161979587, 37034247553292672], ![-59666205081067641, 168904538163532694, -174828067542908741]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [1, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22], [0, 1]]
 g := ![![[20, 1], [3, 12], [21, 9], [1]], ![[0, 22], [16, 11], [2, 14], [1]]]
 h' := ![![[3, 22], [20, 1], [2, 9], [22, 3], [0, 1]], ![[0, 1], [0, 22], [6, 14], [8, 20], [3, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [19, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [1, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-634, 28, 45]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53, -34, 45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![576748401, -11284672, -16863604]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![576748401, -11284672, -16863604]] 
 ![![23, 0, 0], ![10, 1, 0], ![14, 0, 1]] where
  M :=![![![576748401, -11284672, -16863604], ![2967994304, 245055253, -22569344], ![502105120, 1269588384, 256339925]]]
  hmulB := by decide  
  f := ![![![-91471222151776121, 18517123776646336, -4387202389006980]], ![![-6198460915327510, 1254795391313085, -297294623338136]], ![![-214160204567271090, 43353864993997536, -10271691347348107]]]
  g := ![![![40247199, -11284672, -16863604], ![36235330, 245055253, -22569344], ![-686197290, 1269588384, 256339925]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-91471222151776121, 18517123776646336, -4387202389006980]] ![![576748401, -11284672, -16863604]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-516048039291, 52363403492, 24042171818]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-516048039291, 52363403492, 24042171818]] 
 ![![29, 0, 0], ![0, 29, 0], ![26, 10, 1]] where
  M :=![![![-516048039291, 52363403492, 24042171818], ![-4231422239968, -6883371257, 104726806984], ![-7100247894608, -1120806453636, -59246774749]]]
  hmulB := by decide  
  f := ![![![4061596506301246102873, -822215812457187545060, 194804939482064559426]], ![![-34285669348843362458976, 6940674544003285186907, -1644431624914375090120]], ![![-2600081608886708163966, 526351696725439003858, -124706809177572400833]]]
  g := ![![![-39349810571, -6484769472, 24042171818], ![-239804111088, -36350049693, 104726806984], ![-191718336246, -18218576074, -59246774749]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [18, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 28], [0, 1]]
 g := ![![[18, 24], [9], [0, 20], [24, 1]], ![[14, 5], [9], [16, 9], [19, 28]]]
 h' := ![![[24, 28], [12, 13], [0, 26], [3, 7], [0, 1]], ![[0, 1], [5, 16], [15, 3], [26, 22], [24, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [18, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [18, 5, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3062, -1606, 518]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-570, -234, 518]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4061596506301246102873, -822215812457187545060, 194804939482064559426]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![4061596506301246102873, -822215812457187545060, 194804939482064559426]] 
 ![![29, 0, 0], ![9, 1, 0], ![13, 0, 1]] where
  M :=![![![4061596506301246102873, -822215812457187545060, 194804939482064559426], ![-34285669348843362458976, 6940674544003285186907, -1644431624914375090120], ![161852817666886689160048, -32764935111108244585628, 7762890356460472731967]]]
  hmulB := by decide  
  f := ![![![-516048039291, 52363403492, 24042171818]], ![![-306063951503, 16013353799, 11072632874]], ![![-476168013979, -15175248560, 8734533065]]]
  g := ![![![307899124315486025375, -822215812457187545060, 194804939482064559426], ![-2599107900723656998951, 6940674544003285186907, -1644431624914375090120], ![12269643414926715341901, -32764935111108244585628, 7762890356460472731967]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-516048039291, 52363403492, 24042171818]] ![![4061596506301246102873, -822215812457187545060, 194804939482064559426]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![11, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![11, 1, 0]] 
 ![![31, 0, 0], ![11, 1, 0], ![27, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![11, 1, 0], ![0, 12, 2], ![-176, 19, 11]]]
  hmulB := by decide  
  f := ![![![122, 11, 0], ![-341, 0, 0]], ![![44, 4, 0], ![-123, 0, 0]], ![![102, 3, -1], ![-285, 16, 0]]]
  g := ![![![1, 0, 0], ![-11, 31, 0], ![-27, 0, 31]], ![![0, 1, 0], ![-6, 12, 2], ![-22, 19, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![297992420115875, -111754977126338, -31151259761600]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![297992420115875, -111754977126338, -31151259761600]] 
 ![![31, 0, 0], ![23, 1, 0], ![3, 0, 1]] where
  M :=![![![297992420115875, -111754977126338, -31151259761600], ![5482621718041600, -405636492480863, -223509954252676], ![16927565115214688, 617966293620378, -293881515354525]]]
  hmulB := by decide  
  f := ![![![-257330685110156835893657586603, 52093150562780063084966864250, -12342262078960990638884319688]], ![![-120850568762466866874531749251, 24464578996655027613120809075, -5796313764211053500787278204]], ![![-355693729591236412479256806463, 72005431462249308519067456324, -17060014543461246127390729669]]]
  g := ![![![95542279784079, -111754977126338, -31151259761600], ![499444867995467, -405636492480863, -223509954252676], ![115999513161599, 617966293620378, -293881515354525]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-4, 1, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-4, 1, 0]] 
 ![![31, 0, 0], ![27, 1, 0], ![25, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-4, 1, 0], ![0, -3, 2], ![-176, 19, -4]]]
  hmulB := by decide  
  f := ![![![49, -12, 0], ![372, 0, 0]], ![![45, -11, 0], ![342, 0, 0]], ![![39, -8, -1], ![296, 16, 0]]]
  g := ![![![1, 0, 0], ![-27, 31, 0], ![-25, 0, 31]], ![![-1, 1, 0], ![1, -3, 2], ![-19, 19, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![11, 1, 0]] ![![297992420115875, -111754977126338, -31151259761600]]
  ![![31, 0, 0], ![-13, 2, 1]] where
 M := ![![![9237765023592125, -3464404290916478, -965689052609600]], ![![8760538339316225, -1634941240870581, -566173811630276]]]
 hmul := by decide  
 g := ![![![![250704918105516, -104479976817052, -27513759606957], ![-112762504793933, 0, 0]]], ![![![239102211282250, -46048378541401, -14917840599571], ![-103720753043575, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-13, 2, 1]] ![![31, 0, 0], ![-4, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-124, 31, 0]], ![![-403, 62, 31], ![-124, 0, 0]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-4, 1, 0]]], ![![![-13, 2, 1]], ![![-4, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB241I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB241I0 : PrimesBelowBoundCertificateInterval O 1 31 241 where
  m := 11
  g := ![3, 1, 3, 2, 2, 2, 1, 3, 2, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB241I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2]
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
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![11, 121]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![841, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I7N0, I7N1, I11N0, I11N1, I13N0, I13N1, I19N0, I19N1, I23N1, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N1, I2N2], [I3N0], [I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N0, I11N1], [I13N0, I13N1], [], [I19N0, I19N0, I19N1], [I23N1], [I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
