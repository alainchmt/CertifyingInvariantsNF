
import IdealArithmetic.Examples.NF5_1_1012500000_2.RI5_1_1012500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 4, -7, -3, 26]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 4, -7, -3, 26]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![12, 28, 14, 1, 0], ![17, 19, 27, 0, 1]] where
  M :=![![![29, 4, -7, -3, 26], ![42, -21, 47, 13, -150], ![-630, -40, 54, 35, -246], ![198, 412, -943, -294, 3126], ![-146, 32, -83, -21, 257]]]
  hmulB := by decide  
  f := ![![![-7, 0, -3, -1, 10]], ![![30, -13, 5, 1, -18]], ![![-126, -28, 38, 17, -174]], ![![-54, -28, 19, 8, -90]], ![![-105, -35, 37, 16, -169]]]
  g := ![![![-13, -14, -23, -3, 26], ![84, 85, 135, 13, -150], ![108, 126, 214, 35, -246], ![-1704, -1750, -2801, -294, 3126], ![-147, -147, -232, -21, 257]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [27, 28, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 5, 8], [7, 23, 21], [0, 1]]
 g := ![![[6, 22, 4], [13, 28], [24, 24, 13], [1]], ![[14, 28, 20, 12], [3, 24], [8, 8, 22, 17], [21, 8, 16, 19]], ![[17, 17, 8, 26], [9, 1], [17, 2], [11, 18, 24, 10]]]
 h' := ![![[12, 5, 8], [10, 28, 27], [19, 18, 17], [2, 1, 19], [0, 1]], ![[7, 23, 21], [7, 10, 4], [28, 6, 13], [1, 22, 10], [12, 5, 8]], ![[0, 1], [22, 20, 27], [27, 5, 28], [17, 6], [7, 23, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16], []]
 b := ![[], [10, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [27, 28, 10, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-883073656, -105781188, -9655202, 20972439, -128825979]
  a := ![-255, -244, 212, 67, -731]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![36389611, 60506349, 109483865, 20972439, -128825979]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 0, -3, -1, 10]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-7, 0, -3, -1, 10]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![9, 15, 1, 0, 0], ![10, 16, 0, 1, 0], ![3, 9, 0, 0, 1]] where
  M :=![![![-7, 0, -3, -1, 10], ![30, -13, 5, 1, -18], ![-126, -28, 38, 17, -174], ![-558, -56, -85, -22, 210], ![-94, -12, 3, 3, -31]]]
  hmulB := by decide  
  f := ![![![29, 4, -7, -3, 26]], ![![42, -21, 47, 13, -150]], ![![9, -11, 24, 7, -78]], ![![40, 4, -9, -4, 34]], ![![11, -5, 11, 3, -35]]]
  g := ![![![0, -1, -3, -1, 10], ![1, 2, 5, 1, -18], ![-4, 24, 38, 17, -174], ![-7, -11, -85, -22, 210], ![-2, 6, 3, 3, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [10, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 28], [0, 1]]
 g := ![![[16, 6], [5], [19, 28], [14, 1]], ![[13, 23], [5], [5, 1], [28, 28]]]
 h' := ![![[14, 28], [3, 8], [13, 11], [5, 12], [0, 1]], ![[0, 1], [28, 21], [22, 18], [28, 17], [14, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [25, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [10, 15, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38881770, 7115480, -6369730, -3222308, 28515624]
  a := ![-1719, -1664, 1434, 460, -4928]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1478812, -3531802, -6369730, -3222308, 28515624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 4, -7, -3, 26]] ![![-7, 0, -3, -1, 10]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [13, 0, 0, 18, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12, 4, 27, 18], [9, 24, 13, 4, 26], [13, 3, 22, 29, 1], [20, 22, 23, 2, 17], [0, 1]]
 g := ![![[11, 22, 16, 26, 7], [15, 18, 22, 9, 18], [15, 23, 1], []], ![[18, 29, 18, 2, 18, 21, 14, 28], [12, 4, 25, 3, 0, 12, 30, 16], [6, 21, 9, 18, 27, 4, 21, 5], [12, 27, 18, 5, 29, 18, 17, 4]], ![[25, 14, 25, 24, 20, 10, 10, 30], [13, 21, 1, 5, 23, 11, 24, 30], [17, 27, 7, 13, 23, 15, 10, 30], [14, 15, 9, 18, 16, 25, 29, 30]], ![[9, 16, 11, 16, 19, 1, 26, 25], [6, 27, 11, 24, 29, 15, 26, 18], [27, 0, 20, 19, 25, 7, 26, 8], [24, 16, 1, 16, 8, 17, 17, 1]], ![[24, 2, 30, 4, 20, 4, 2, 12], [11, 9, 16, 1, 24, 17], [30, 4, 26, 10, 2, 1, 15, 6], [21, 16, 12, 18, 26, 19, 2, 15]]]
 h' := ![![[12, 12, 4, 27, 18], [22, 2, 12, 30, 21], [22, 11, 18, 9, 24], [0, 0, 0, 1], [0, 1]], ![[9, 24, 13, 4, 26], [20, 25, 11, 10, 25], [26, 14, 15, 19, 5], [22, 28, 13, 13, 23], [12, 12, 4, 27, 18]], ![[13, 3, 22, 29, 1], [17, 6, 3, 28, 5], [0, 9, 17, 7, 26], [20, 26, 25, 3, 26], [9, 24, 13, 4, 26]], ![[20, 22, 23, 2, 17], [1, 29, 4, 22, 26], [24, 4, 13, 28, 7], [25, 11, 22, 18, 15], [13, 3, 22, 29, 1]], ![[0, 1], [20, 0, 1, 3, 16], [22, 24, 30, 30], [8, 28, 2, 27, 29], [20, 22, 23, 2, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 3, 6, 16], [], [], []]
 b := ![[], [12, 9, 20, 18, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [13, 0, 0, 18, 8, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1546847066725, -2063186917731, -14982483034230, -4664104524243, 43705248392199]
  a := ![-158, -152, 132, 42, -453]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![49898292475, -66554416701, -483305904330, -150454984653, 1409846722329]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46396153, -7521856, 4019535, 294053, -8926778]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![46396153, -7521856, 4019535, 294053, -8926778]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![8, 1, 1, 0, 0], ![29, 7, 0, 1, 0], ![2, 19, 0, 0, 1]] where
  M :=![![![46396153, -7521856, 4019535, 294053, -8926778], ![-80656566, 270487, 32911615, 14815819, -138376998], ![-327100266, 86487884, -142276952, -45914045, 501433350], ![1884936150, -264241336, 20007809, -43206572, 188576790], ![84655382, 1846084, -45451655, -19772575, 186882649]]]
  hmulB := by decide  
  f := ![![![25714462253, 2558896340, -4628146021, -2120661613, 17680903126]], ![![21311292342, -15215211457, 37842195433, 10905926439, -122789021130]], ![![-7159672532, -482033613, 734607589, 422125316, -3095926540]], ![![33714294745, 7416622277, -15832700143, -5747333844, 55382924234]], ![![9787562694, -6976895743, 17353348660, 5000734420, -56306140469]]]
  g := ![![![636916, 4216460, 4019535, 294053, -8926778], ![-13428493, 67373273, 32911615, 14815819, -138376998], ![30804215, -242623527, -142276952, -45914045, 501433350], ![70289478, -96344923, 20007809, -43206572, 188576790], ![17511027, -90947691, -45451655, -19772575, 186882649]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [21, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 36], [0, 1]]
 g := ![![[35, 30], [28], [11, 10], [25], [1]], ![[0, 7], [28], [24, 27], [25], [1]]]
 h' := ![![[5, 36], [11, 20], [28, 19], [27, 26], [16, 5], [0, 1]], ![[0, 1], [0, 17], [12, 18], [9, 11], [4, 32], [5, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [25, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [21, 32, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10628984, 2074500, -1862716, -914334, 8214914]
  a := ![907, 873, -755, -242, 2600]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![962610, -3939076, -1862716, -914334, 8214914]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-269009, -3434, -7685, 5139, 42]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-269009, -3434, -7685, 5139, 42]] 
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-269009, -3434, -7685, 5139, 42], ![463014, 173281, -389153, -131105, 1326870], ![4122990, -197056, 718066, 103627, -1980210], ![-14436090, -2806768, 5892389, 2191438, -20789274], ![-407334, -345044, 805393, 256029, -2694281]]]
  hmulB := by decide  
  f := ![![![199531, 110662, -30177, -13999, 184698]], ![![74385, 39707, -10916, -5124, 67116]], ![![273360, 145272, -38092, -18053, 238842]], ![![606032, 325624, -86583, -40776, 538638]], ![![100457, 53022, -13782, -6558, 86845]]]
  g := ![![![-3821, -3434, -7685, 5139, 42], ![198715, 173281, -389153, -131105, 1326870], ![-228074, -197056, 718066, 103627, -1980210], ![-3215618, -2806768, 5892389, 2191438, -20789274], ![-395921, -345044, 805393, 256029, -2694281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![993967, -221131, 290518, 84951, -977896]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![993967, -221131, 290518, 84951, -977896]] 
 ![![37, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![993967, -221131, 290518, 84951, -977896], ![-4089162, 476585, 252816, 207486, -1552146], ![47988, 1337466, -4219843, -1622556, 16279884], ![49328568, -9252756, 9069978, 2161733, -27902232], ![5075290, -507058, -475832, -319018, 2561653]]]
  hmulB := by decide  
  f := ![![![-81791023, 102617411, -251552300, -74159585, 821859326]], ![![17633177, 89094568, -213150008, -65253731, 704570000]], ![![-91190875, -51506611, 118424841, 38515987, -399110122]], ![![-1422306834, 41825874, -184837074, -16644457, 475771044]], ![![-230255711, 63059061, -165246528, -43811435, 523282511]]]
  g := ![![![904108, -221131, 290518, 84951, -977896], ![582349, 476585, 252816, 207486, -1552146], ![-12622031, 1337466, -4219843, -1622556, 16279884], ![28850916, -9252756, 9069978, 2161733, -27902232], ![-1242719, -507058, -475832, -319018, 2561653]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-944661, 154218, -89963, -9143, 212602]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![-944661, 154218, -89963, -9143, 212602]] 
 ![![37, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-944661, 154218, -89963, -9143, 212602], ![1728354, -30143, -648271, -295735, 2743554], ![6306498, -1756424, 2945104, 962261, -10454334], ![-38848518, 5426272, -745661, 759508, -2640678], ![-1884994, -28856, 906135, 399075, -3759513]]]
  hmulB := by decide  
  f := ![![![34407, 19826, -27111, -9121, 98210]], ![![40353, 18647, -23736, -8260, 87696]], ![![9513, 10990, -5767, -1938, 25956]], ![![-56628, 35600, -42005, -11006, 147314]], ![![-5303, 5550, -4662, -1234, 17581]]]
  g := ![![![-138276, 154218, -89963, -9143, 212602], ![150712, -30143, -648271, -295735, 2743554], ![1218118, -1756424, 2945104, 962261, -10454334], ![-5314819, 5426272, -745661, 759508, -2640678], ![-139318, -28856, 906135, 399075, -3759513]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![46396153, -7521856, 4019535, 294053, -8926778]] ![![-269009, -3434, -7685, 5139, 42]]
  ![![-129629, 29630, -39664, -11756, 134452]] where
 M := ![![![-129629, 29630, -39664, -11756, 134452]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-129629, 29630, -39664, -11756, 134452]] ![![993967, -221131, 290518, 84951, -977896]]
  ![![-149435968663, 30337389845, -33395992422, -8813183099, 107486284176]] where
 M := ![![![-149435968663, 30337389845, -33395992422, -8813183099, 107486284176]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![-149435968663, 30337389845, -33395992422, -8813183099, 107486284176]] ![![-944661, 154218, -89963, -9143, 212602]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![122756422768707555, -16227006460709025, -609081834777215, -3539790199929500, 19771436528309786]]]
 hmul := by decide  
 g := ![![![![3317741155911015, -438567742181325, -16461671210195, -95670005403500, 534363149413778]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2, I37N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
    exact isPrimeI37N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1 ⊙ MulI37N2)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [11, 2, 18, 18, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 32, 8, 18, 31], [34, 9, 21, 14, 40], [38, 4, 38, 9, 20], [1, 36, 15, 0, 32], [0, 1]]
 g := ![![[26, 22, 10, 4, 5], [18, 1, 23, 40], [22, 22, 22, 23], [1], []], ![[38, 23, 8, 9, 6, 39, 39, 2], [28, 39], [33, 35, 9, 40], [16, 23, 40, 17, 2, 16, 8, 18], [11, 18, 29, 18]], ![[24, 20, 23, 40, 26, 26, 3, 10], [21, 33, 16, 1], [39, 7, 0, 10], [34, 12, 15, 28, 27, 23, 10, 4], [22, 14, 5, 1]], ![[17, 11, 6, 38, 22, 9, 18, 21], [29, 11, 18, 33], [34, 16, 29, 33], [7, 33, 36, 12, 5, 4, 38, 23], [5, 24, 30, 31]], ![[3, 18, 13, 24, 23, 1, 18, 9], [40, 39, 21, 39], [33, 21, 37, 39], [37, 2, 14, 11, 15, 19, 3, 1], [32, 12, 8, 40]]]
 h' := ![![[1, 32, 8, 18, 31], [11, 10, 31, 8, 13], [2, 4, 5, 35, 9], [30, 39, 23, 23, 33], [0, 0, 1], [0, 1]], ![[34, 9, 21, 14, 40], [40, 11, 31, 39, 7], [15, 22, 33, 30], [38, 10, 7, 25, 32], [3, 8, 36, 16, 21], [1, 32, 8, 18, 31]], ![[38, 4, 38, 9, 20], [19, 32, 9, 23, 21], [2, 17, 3, 29, 40], [12, 14, 3, 18, 25], [12, 4, 5, 5, 23], [34, 9, 21, 14, 40]], ![[1, 36, 15, 0, 32], [19, 2, 24, 8, 32], [16, 30, 24, 12, 22], [12, 8, 6, 2, 22], [36, 30, 17, 24, 35], [38, 4, 38, 9, 20]], ![[0, 1], [19, 27, 28, 4, 9], [7, 9, 17, 17, 11], [40, 11, 2, 14, 11], [18, 40, 23, 37, 3], [1, 36, 15, 0, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 6, 18, 9], [], [], []]
 b := ![[], [8, 19, 2, 18, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [11, 2, 18, 18, 8, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3381547901566672, 56656028702436, -1960256283525065, -694180654731168, 6184303128386442]
  a := ![-427, -408, 356, 115, -1224]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![82476778086992, 1381854358596, -47811128866465, -16931235481248, 150836661667962]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19511, -9981, 2623, 1260, -16566]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-19511, -9981, 2623, 1260, -16566]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![36, 23, 5, 1, 0], ![22, 12, 2, 0, 1]] where
  M :=![![![-19511, -9981, 2623, 1260, -16566], ![-85392, -43679, 11481, 5515, -72504], ![-373698, -191134, 50224, 24129, -317226], ![-1635102, -836412, 219773, 105580, -1388142], ![-253200, -129514, 34031, 16349, -214949]]]
  hmulB := by decide  
  f := ![![![-155, 19, -5, 2, 0]], ![![180, 17, -131, -53, 516]], ![![1422, -250, 380, 109, -1290]], ![![0, 7, -16, -6, 60]], ![![34, 2, -17, -7, 67]]]
  g := ![![![6967, 3717, 685, 1260, -16566], ![30492, 16268, 2998, 5515, -72504], ![133410, 71177, 13117, 24129, -317226], ![583794, 311464, 57399, 105580, -1388142], ![90398, 48229, 8888, 16349, -214949]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [14, 31, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 19, 13], [28, 23, 30], [0, 1]]
 g := ![![[0, 29, 11], [27, 32, 4], [13, 21], [22, 28, 1], []], ![[41, 42, 33, 41], [37, 27, 30, 13], [9, 1], [10, 38, 9, 40], [23, 40]], ![[27, 16, 8, 12], [6, 10, 23, 12], [29, 6], [20, 13, 21, 37], [6, 40]]]
 h' := ![![[0, 19, 13], [9, 21, 21], [39, 20, 41], [36, 1, 35], [0, 0, 1], [0, 1]], ![[28, 23, 30], [41, 25, 25], [38, 2, 42], [32, 12, 1], [22, 17, 23], [0, 19, 13]], ![[0, 1], [32, 40, 40], [16, 21, 3], [11, 30, 7], [12, 26, 19], [28, 23, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 32], []]
 b := ![[], [40, 26, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [14, 31, 15, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1474356964, -304419846, 667089028, 253765122, -2405219706]
  a := ![270, 258, -224, -82, 774]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![983835632, 528409740, 97876810, 253765122, -2405219706]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155, 19, -5, 2, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-155, 19, -5, 2, 0]] 
 ![![43, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![-155, 19, -5, 2, 0], ![180, 17, -131, -53, 516], ![1422, -250, 380, 109, -1290], ![-5670, 476, 605, 344, -2838], ![-132, -36, 191, 73, -731]]]
  hmulB := by decide  
  f := ![![![-19511, -9981, 2623, 1260, -16566]], ![![-10607, -5426, 1426, 685, -9006]], ![![-20488, -10480, 2754, 1323, -17394]], ![![-48008, -24558, 6453, 3100, -40758]], ![![-253200, -129514, 34031, 16349, -214949]]]
  g := ![![![-10, 19, -5, 2, 0], ![103, 17, -131, -53, 12], ![-142, -250, 380, 109, -30], ![-884, 476, 605, 344, -66], ![-140, -36, 191, 73, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [3, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 42], [0, 1]]
 g := ![![[33, 23], [19, 36], [4], [31, 40], [1]], ![[35, 20], [24, 7], [4], [27, 3], [1]]]
 h' := ![![[30, 42], [29, 25], [37, 6], [36, 2], [40, 30], [0, 1]], ![[0, 1], [5, 18], [2, 37], [10, 41], [37, 13], [30, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [41, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [3, 13, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![67621, -120027, 274359, 82928, -846498]
  a := ![-59, -57, 54, 28, -170]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-153712, -120027, 274359, 82928, -19686]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-19511, -9981, 2623, 1260, -16566]] ![![-155, 19, -5, 2, 0]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1851197, -354553, 881866, 216201, -2758178]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1851197, -354553, 881866, 216201, -2758178]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![3, 4, 37, 1, 0], ![39, 20, 23, 0, 1]] where
  M :=![![![1851197, -354553, 881866, 216201, -2758178], ![-13640046, -1620941, 2737618, 1209398, -10416414], ![-16151148, 7036870, -19410893, -5455106, 62030748], ![253409436, 10955720, -18045416, -12549845, 81320604], ![22183286, 3049228, -7057210, -2764674, 25046057]]]
  hmulB := by decide  
  f := ![![![72840521, -53436765, 140940552, 52215495, -532800664]], ![![-1694213418, 300967779, -239994242, -46630000, 684381774]], ![![4015881288, -229339226, -992454639, -489637790, 4394622576]], ![![3206326497, -220808055, -670783829, -344188608, 3040096860]], ![![1352167943, -36542521, -465367929, -215297611, 1985307721]]]
  g := ![![![2314288, 1147749, 1198309, 216201, -2758178], ![8275998, 4295101, 4203562, 1209398, -10416414], ![-51467766, -25782078, -26474025, -5455106, 62030748], ![-61286055, -33303340, -30299469, -12549845, 81320604], ![-20134445, -10357728, -10230289, -2764674, 25046057]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [46, 16, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 34, 17], [6, 12, 30], [0, 1]]
 g := ![![[38, 15, 42], [4, 39, 17], [5, 43, 12], [40, 44, 1], []], ![[13, 27, 13, 27], [2, 29, 21, 42], [28, 28, 46, 42], [44, 23, 35, 4], [7, 7]], ![[44, 40, 4, 30], [37, 11, 28, 46], [11, 11, 15, 39], [26, 40, 18, 41], [41, 7]]]
 h' := ![![[38, 34, 17], [4, 0, 18], [5, 12, 39], [40, 15, 23], [0, 0, 1], [0, 1]], ![[6, 12, 30], [37, 19, 28], [39, 34, 14], [2, 46, 14], [41, 35, 12], [38, 34, 17]], ![[0, 1], [27, 28, 1], [25, 1, 41], [21, 33, 10], [30, 12, 34], [6, 12, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24], []]
 b := ![[], [39, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [46, 16, 3, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5028136, -39261, 75719, 176604, -869910]
  a := ![23, 21, -19, -8, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![603586, 354309, 288283, 176604, -869910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![858111, 7073, 33825, -13564, -30844]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![858111, 7073, 33825, -13564, -30844]] 
 ![![47, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![858111, 7073, 33825, -13564, -30844], ![-1590888, -555145, 1240281, 421049, -4239768], ![-12982806, 701182, -2455444, -385359, 6876210], ![47832210, 8886000, -18530363, -6959248, 65606418], ![1530208, 1112972, -2585313, -828041, 8669511]]]
  hmulB := by decide  
  f := ![![![-86056905, 17077797, -17964847, -4588222, 57015722]], ![![-29017713, 6382126, -8069100, -2320323, 26976910]], ![![-22224843, 2611771, 1162105, 1045193, -7633008]], ![![-164661366, 30410380, -27064077, -5969220, 80924006]], ![![-47169334, 8527744, -7160345, -1482203, 20898391]]]
  g := ![![![31739, 7073, 33825, -13564, -30844], ![1385136, -555145, 1240281, 421049, -4239768], ![-2633924, 701182, -2455444, -385359, 6876210], ![-20854907, 8886000, -18530363, -6959248, 65606418], ![-2875149, 1112972, -2585313, -828041, 8669511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54281, 3253, -4604, -2907, 20288]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![54281, 3253, -4604, -2907, 20288]] 
 ![![47, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![54281, 3253, -4604, -2907, 20288], ![-18174, -33417, 79262, 24588, -263094], ![-944208, -8358, -35859, 15338, 29448], ![1733796, 610444, -1364844, -462867, 4663956], ![-70610, 61410, -151822, -44168, 494027]]]
  hmulB := by decide  
  f := ![![![33338141, 17052709, -4481402, -2152829, 28303654]], ![![30058268, 15375043, -4040510, -1941028, 25519078]], ![![22804603, 11664829, -3065485, -1472629, 19360958]], ![![75756953, 38750413, -10183494, -4892060, 64316890]], ![![24100093, 12327423, -3239612, -1556281, 20460733]]]
  g := ![![![-7844, 3253, -4604, -2907, 20288], ![110228, -33417, 79262, 24588, -263094], ![-24077, -8358, -35859, 15338, 29448], ![-1936537, 610444, -1364844, -462867, 4663956], ![-208281, 61410, -151822, -44168, 494027]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1851197, -354553, 881866, 216201, -2758178]] ![![858111, 7073, 33825, -13564, -30844]]
  ![![-3175722980879, -320342391838, 581969239379, 265059270351, -2217861381644]] where
 M := ![![![-3175722980879, -320342391838, 581969239379, 265059270351, -2217861381644]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-3175722980879, -320342391838, 581969239379, 265059270351, -2217861381644]] ![![54281, 3253, -4604, -2907, 20288]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-99897633216030783, 21115129731909181, -56683189111773077, -14447195616606514, 177530293083114580]]]
 hmul := by decide  
 g := ![![![![-2125481557787889, 449258079402323, -1206025300250491, -307387140778862, 3777240278364140]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46477, -37748, 26430, 10580, -119652]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-46477, -37748, 26430, 10580, -119652]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![5, 38, 45, 28, 1]] where
  M :=![![![-46477, -37748, 26430, 10580, -119652], ![-483624, -93813, 6316, 11814, -142008], ![-640836, -603684, 14193, 6796, -360180], ![-3710520, -2937820, 1407876, 571449, -6890952], ![-475200, -441908, 133224, 53222, -726217]]]
  hmulB := by decide  
  f := ![![![437599, 61260, -121346, -49028, 441324]], ![![883368, -248217, 649092, 172678, -2057448]], ![![-9148356, -725908, 1203069, 619716, -4827828]], ![![-2159496, 5524596, -13409812, -4014459, 44018856]], ![![-8283893, 2137350, -5629349, -1480274, 17784959]]]
  g := ![![![10411, 85076, 102090, 63412, -119652], ![4272, 100047, 120692, 75246, -142008], ![21888, 246852, 306081, 190412, -360180], ![580080, 4885252, 5877372, 3651285, -6890952], ![59545, 512346, 619113, 384666, -726217]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [20, 16, 31, 23, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 41, 47, 13], [32, 28, 48, 41], [2, 36, 11, 52], [0, 1]]
 g := ![![[32, 48, 46, 15], [46, 48, 44], [28, 8, 21, 4], [21, 30, 1], []], ![[43, 17, 12, 3, 34, 15], [46, 33, 25], [6, 33, 14, 26, 5, 40], [36, 26, 49], [10, 18, 8, 17, 10, 24]], ![[21, 17, 32, 47, 7, 27], [15, 33, 44], [33, 2, 21, 30, 33, 12], [34, 47, 17], [32, 33, 51, 49, 7, 21]], ![[7, 11, 1, 29, 11, 6], [48, 36, 44], [52, 7, 7, 20, 32, 49], [36, 19, 13], [41, 21, 5, 25, 3, 52]]]
 h' := ![![[49, 41, 47, 13], [33, 10, 28, 42], [23, 44, 0, 37], [4, 18, 15, 2], [0, 0, 0, 1], [0, 1]], ![[32, 28, 48, 41], [28, 29, 6, 29], [43, 48, 24, 48], [23, 51, 20, 30], [1, 17, 35, 46], [49, 41, 47, 13]], ![[2, 36, 11, 52], [19, 5, 48, 45], [52, 51, 22, 37], [3, 32, 44, 23], [10, 44, 18, 21], [32, 28, 48, 41]], ![[0, 1], [32, 9, 24, 43], [12, 16, 7, 37], [46, 5, 27, 51], [36, 45, 0, 38], [2, 36, 11, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [34, 6, 20], []]
 b := ![[], [], [50, 0, 19, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [20, 16, 31, 23, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![444856476083, 53961794764, 829577156855, 245893324925, -2448865204944]
  a := ![381, 364, -313, -103, 1092]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![239418537751, 1756808294012, 2094877573195, 1298379604969, -2448865204944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-437599, -61260, 121346, 49028, -441324]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-437599, -61260, 121346, 49028, -441324]] 
 ![![53, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-437599, -61260, 121346, 49028, -441324], ![-883368, 248217, -649092, -172678, 2057448], ![9148356, 725908, -1203069, -619716, 4827828], ![2159496, -5524596, 13409812, 4014459, -44018856], ![2660400, -382668, 1077632, 253514, -3303523]]]
  hmulB := by decide  
  f := ![![![46477, 37748, -26430, -10580, 119652]], ![![20525, 11029, -6602, -2818, 32028]], ![![49799, 42016, -21711, -8712, 103872]], ![![91056, 72524, -38532, -15573, 184200]], ![![32643, 27568, -15978, -6394, 74657]]]
  g := ![![![110943, -61260, 121346, 49028, -441324], ![-520869, 248217, -649092, -172678, 2057448], ![-1208201, 725908, -1203069, -619716, 4827828], ![11123008, -5524596, 13409812, 4014459, -44018856], ![837881, -382668, 1077632, 253514, -3303523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-46477, -37748, 26430, 10580, -119652]] ![![-437599, -61260, 121346, 49028, -441324]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37689109, 27762001, -73289147, -27157142, 277083256]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-37689109, 27762001, -73289147, -27157142, 277083256]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![39, 52, 27, 20, 1]] where
  M :=![![![-37689109, 27762001, -73289147, -27157142, 277083256], ![880856292, -156537273, 124964859, 24315749, -356544492], ![-2090116494, 119654770, 515592996, 254475867, -2283604566], ![-4500426762, 1525971540, -2980803293, -1024618680, 10848264102], ![-1159562452, 196626084, -134055175, -20304857, 352015691]]]
  hmulB := by decide  
  f := ![![![4250759, 215305, -265727, -198840, 1276094]], ![![-2582472, -2640729, 6195647, 1954245, -20674464]], ![![-72211518, 86886, -4487856, 642695, 8008074]], ![![153939438, 47124844, -104171757, -35928684, 358009086]], ![![19616837, 13912837, -32285608, -10354732, 108314359]]]
  g := ![![![-183795527, -243738429, -128043001, -94386818, 277083256], ![250611720, 311589429, 165282477, 121274671, -356544492], ![1474075620, 2014696478, 1053778242, 778416393, -2283604566], ![-7247164860, -9535317996, -5014981933, -3694744080, 10848264102], ![-252341939, -306918472, -163364048, -119671503, 352015691]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [21, 38, 32, 27, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 23, 20, 47], [32, 58, 1, 35], [10, 36, 38, 36], [0, 1]]
 g := ![![[37, 8, 13, 15], [28, 38, 8, 28], [49, 39, 25], [2, 48, 32, 1], []], ![[24, 14, 6, 10, 30, 24], [47, 22, 37, 38, 36, 39], [30, 10, 46], [22, 28, 40, 30, 36, 11], [11, 20, 26, 36, 13, 42]], ![[33, 5, 15, 29, 18, 22], [5, 40, 53, 3, 13, 27], [41, 12, 53], [1, 11, 26, 51, 31, 5], [1, 57, 37, 4, 31, 41]], ![[50, 12, 31, 41, 49, 45], [40, 6, 37, 58, 40, 36], [16, 0, 21], [6, 8, 3, 16, 54, 48], [47, 38, 20, 21, 5, 46]]]
 h' := ![![[49, 23, 20, 47], [2, 47, 5, 30], [27, 52, 21, 21], [17, 37, 36, 5], [0, 0, 0, 1], [0, 1]], ![[32, 58, 1, 35], [41, 11, 22, 23], [26, 47, 36, 10], [19, 29, 10, 39], [8, 44, 36, 57], [49, 23, 20, 47]], ![[10, 36, 38, 36], [36, 12, 33, 2], [27, 7, 36, 27], [48, 22, 53, 42], [2, 0, 16, 28], [32, 58, 1, 35]], ![[0, 1], [20, 48, 58, 4], [33, 12, 25, 1], [30, 30, 19, 32], [13, 15, 7, 32], [10, 36, 38, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [56, 45, 5], []]
 b := ![[], [], [2, 35, 24, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [21, 38, 32, 27, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![472164602869, 12637739811, 260864355487, 68292330072, -744738875460]
  a := ![277, 265, -231, -74, 794]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![500287809251, 656594224809, 345234135473, 253611353208, -744738875460]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4250759, -215305, 265727, 198840, -1276094]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-4250759, -215305, 265727, 198840, -1276094]] 
 ![![59, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-4250759, -215305, 265727, 198840, -1276094], ![2582472, 2640729, -6195647, -1954245, 20674464], ![72211518, -86886, 4487856, -642695, -8008074], ![-153939438, -47124844, 104171757, 35928684, -358009086], ![3175448, -4935594, 12053911, 3574253, -39451925]]]
  hmulB := by decide  
  f := ![![![37689109, -27762001, 73289147, 27157142, -277083256]], ![![-9819380, -1111165, 7819463, 3270193, -31527484]], ![![69920820, -27437336, 58339338, 20542539, -214896462]], ![![101830358, -44685620, 100209647, 35778040, -371721938]], ![![25402787, -7567527, 13451822, 4486765, -48233305]]]
  g := ![![![-226209, -215305, 265727, 198840, -1276094], ![3527478, 2640729, -6195647, -1954245, 20674464], ![-1214528, -86886, 4487856, -642695, -8008074], ![-61309850, -47124844, 104171757, 35928684, -358009086], ![-6714471, -4935594, 12053911, 3574253, -39451925]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-37689109, 27762001, -73289147, -27157142, 277083256]] ![![-4250759, -215305, 265727, 198840, -1276094]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7082623321, 258023268, -1040019464, -119220736, 2763564138]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-7082623321, 258023268, -1040019464, -119220736, 2763564138]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![47, 42, 1, 0, 0], ![39, 52, 0, 1, 0], ![59, 32, 0, 0, 1]] where
  M :=![![![-7082623321, 258023268, -1040019464, -119220736, 2763564138], ![22432903416, 4772906487, -10145370498, -3705850076, 35566589424], ![93272566248, -11737487728, 33745536219, 7661852478, -102511173432], ![-540567358164, -67897508100, 131201790446, 54883423611, -483510223044], ![-31521636720, -10202397434, 22659996450, 7760830020, -77691290251]]]
  hmulB := by decide  
  f := ![![![-47158021, 12461768, -19398372, -6183472, 68105706]], ![![260755992, -34090965, -517774, -7206456, 39201168]], ![![140281273, -14614874, -11499753, -8184582, 64409502]], ![![150197253, -11891696, -23809834, -13178145, 113328978]], ![![85889437, -5137898, -18890070, -9562736, 85141427]]]
  g := ![![![-1911514491, -627798908, -1040019464, -119220736, 2763564138], ![-23846480430, -8435216233, -10145370498, -3705850076, 35566589424], ![69779989341, 23817888722, 33745536219, 7661852478, -102511173432], ![322616362781, 115410104964, 131201790446, 54883423611, -483510223044], ![52206103019, 18371079978, 22659996450, 7760830020, -77691290251]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [45, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 60], [0, 1]]
 g := ![![[13, 19], [9], [46, 12], [25, 46], [25, 1]], ![[0, 42], [9], [41, 49], [16, 15], [50, 60]]]
 h' := ![![[25, 60], [38, 18], [4, 58], [34, 16], [34, 31], [0, 1]], ![[0, 1], [0, 43], [51, 3], [7, 45], [16, 30], [25, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [59, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [45, 36, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25178, 22921, -6676, -218, 31341]
  a := ![43, 41, -35, -7, 123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25443, -11283, -6676, -218, 31341]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35205, -17940, 42680, 15458, -159478]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![35205, -17940, 42680, 15458, -159478]] 
 ![![61, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![35205, -17940, 42680, 15458, -159478], ![-522516, 88769, -60944, -9356, 160692], ![1086264, -41596, -334375, -157784, 1442760], ![3112560, -941080, 1692884, 566921, -6082032], ![682084, -110518, 62268, 5568, -143145]]]
  hmulB := by decide  
  f := ![![![-7773711, -3976064, 1045080, 502030, -6599942]], ![![-5272851, -2696935, 708840, 340514, -4476602]], ![![-6772830, -3464340, 910489, 437380, -5750228]], ![![-13609533, -6961528, 1829876, 878979, -11555746]], ![![-3437566, -1758342, 462156, 222004, -2918653]]]
  g := ![![![18443, -17940, 42680, 15458, -159478], ![-61793, 88769, -60944, -9356, 160692], ![-42222, -41596, -334375, -157784, 1442760], ![860389, -941080, 1692884, 566921, -6082032], ![74264, -110518, 62268, 5568, -143145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![164738155, 84265560, -22144657, -10638085, 139861246]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![164738155, 84265560, -22144657, -10638085, 139861246]] 
 ![![61, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![164738155, 84265560, -22144657, -10638085, 139861246], ![720907302, 368752813, -96906787, -46553109, 612043974], ![3154747878, 1613691720, -424071830, -203720119, 2678353254], ![13805428338, 7061643676, -1855772133, -891495482, 11720687394], ![2137695986, 1093457368, -287356289, -138043259, 1814885119]]]
  hmulB := by decide  
  f := ![![![89183, 25188, -55301, -19279, 190750]], ![![83643, 20357, -44008, -15694, 152988]], ![![-7528, 2740, -7044, -1931, 22522]], ![![-49195, 37300, -92632, -26777, 300844]], ![![50305, 20840, -47148, -15722, 160209]]]
  g := ![![![-165659260, 84265560, -22144657, -10638085, 139861246], ![-724938140, 368752813, -96906787, -46553109, 612043974], ![-3172387125, 1613691720, -424071830, -203720119, 2678353254], ![-13882619044, 7061643676, -1855772133, -891495482, 11720687394], ![-2149648552, 1093457368, -287356289, -138043259, 1814885119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2

def I61N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1031, 40, -37, 11, -38]] i)))

def SI61N3: IdealEqSpanCertificate' Table ![![-1031, 40, -37, 11, -38]] 
 ![![61, 0, 0, 0, 0], ![53, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![-1031, 40, -37, 11, -38], ![534, -389, -519, -225, 1926], ![2862, -3408, 3004, 1029, -11826], ![-49302, -3252, 2199, 1960, -18342], ![-3742, -1284, 1179, 521, -5519]]]
  hmulB := by decide  
  f := ![![![92693, 21532, -46273, -16635, 161314]], ![![87727, 17931, -37910, -13956, 133268]], ![![50216, 15316, -33846, -11679, 116338]], ![![-15877, 34660, -84268, -25163, 276400]], ![![58368, 18528, -41085, -14105, 140977]]]
  g := ![![![8, 40, -37, 11, -38], ![-602, -389, -519, -225, 1926], ![9221, -3408, 3004, 1029, -11826], ![13772, -3252, 2199, 1960, -18342], ![4141, -1284, 1179, 521, -5519]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N3 : Nat.card (O ⧸ I61N3) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N3)

lemma isPrimeI61N3 : Ideal.IsPrime I61N3 := prime_ideal_of_norm_prime hp61.out _ NI61N3
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-7082623321, 258023268, -1040019464, -119220736, 2763564138]] ![![35205, -17940, 42680, 15458, -159478]]
  ![![444498843, 48311772, -89807912, -39637122, 337968796]] where
 M := ![![![444498843, 48311772, -89807912, -39637122, 337968796]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![444498843, 48311772, -89807912, -39637122, 337968796]] ![![164738155, 84265560, -22144657, -10638085, 139861246]]
  ![![92693, 21532, -46273, -16635, 161314]] where
 M := ![![![92693, 21532, -46273, -16635, 161314]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N2 : IdealMulLeCertificate' Table 
  ![![92693, 21532, -46273, -16635, 161314]] ![![-1031, 40, -37, 11, -38]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2, I61N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
    exact isPrimeI61N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1 ⊙ MulI61N2)


lemma PB1981I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1981I1 : PrimesBelowBoundCertificateInterval O 23 61 1981 where
  m := 9
  g := ![2, 1, 4, 1, 2, 3, 2, 2, 4]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1981I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2, I61N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![24389, 841]
    · exact ![28629151]
    · exact ![1369, 37, 37, 37]
    · exact ![115856201]
    · exact ![79507, 1849]
    · exact ![103823, 47, 47]
    · exact ![7890481, 53]
    · exact ![12117361, 59]
    · exact ![3721, 61, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
      exact NI61N3
  β := ![I29N1, I37N0, I37N1, I37N2, I37N3, I43N1, I47N1, I47N2, I53N1, I59N1, I61N1, I61N2, I61N3]
  Il := ![[I29N1], [], [I37N0, I37N1, I37N2, I37N3], [], [I43N1], [I47N1, I47N2], [I53N1], [I59N1], [I61N1, I61N2, I61N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
