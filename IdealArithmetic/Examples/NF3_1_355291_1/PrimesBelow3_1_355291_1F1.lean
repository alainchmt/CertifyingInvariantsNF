
import IdealArithmetic.Examples.NF3_1_355291_1.RI3_1_355291_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29380750741322809, 30906106920724811, 21585159007029302]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![29380750741322809, 30906106920724811, 21585159007029302]] 
 ![![37, 0, 0], ![0, 37, 0], ![11, 29, 1]] where
  M :=![![![29380750741322809, 30906106920724811, 21585159007029302], ![-2762900352899750656, 174099179056470698, 302683384473190885], ![-6718882038752526464, 80945268043621297, 476782563529661583]]]
  hmulB := by decide  
  f := ![![![1581261221903263543036142220635597, -351034497426941009626707179226787, 151265042722381294844644123463647]], ![![-19361925468464805740114447803346816, 4298280184130280815207349116416075, -1852181311099061888008373760732921]], ![![-14014364187631346594535604073848221, 3111140159019374753813238836527381, -1340628207537713015723048063445174]]]
  g := ![![![-5623135090162149, -16082797413057431, 21585159007029302], ![-164659934651482443, -232532945153136891, 302683384473190885], ![-323337573988616321, -371506731738285530, 476782563529661583]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [36, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 36], [0, 1]]
 g := ![![[29, 36], [4], [9, 26], [27], [1]], ![[0, 1], [4], [23, 11], [27], [1]]]
 h' := ![![[29, 36], [11, 6], [9, 35], [28, 27], [1, 29], [0, 1]], ![[0, 1], [0, 31], [25, 2], [34, 10], [28, 8], [29, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [26, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [36, 8, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3036, -3083, 1759]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-605, -1462, 1759]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1581261221903263543036142220635597, 351034497426941009626707179226787, -151265042722381294844644123463647]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-1581261221903263543036142220635597, 351034497426941009626707179226787, -151265042722381294844644123463647]] 
 ![![37, 0, 0], ![15, 1, 0], ![6, 0, 1]] where
  M :=![![![-1581261221903263543036142220635597, 351034497426941009626707179226787, -151265042722381294844644123463647], ![19361925468464805740114447803346816, -4298280184130280815207349116416075, 1852181311099061888008373760732921], ![-25570490202183643492104071137681920, 5676559984364926644029508453058421, -2446098873031218927198975355683154]]]
  hmulB := by decide  
  f := ![![![-29380750741322809, -30906106920724811, -21585159007029302]], ![![62761867345402933, -17234886023441699, -16931372150773795]], ![![176826960386610530, -7199511069404599, -16386311285725335]]]
  g := ![![![-160518606134407862658618518060960, 351034497426941009626707179226787, -151265042722381294844644123463647], ![1965487577400666125410120053653795, -4298280184130280815207349116416075, 1852181311099061888008373760732921], ![-2595737749445141340252779616201603, 5676559984364926644029508453058421, -2446098873031218927198975355683154]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![29380750741322809, 30906106920724811, 21585159007029302]] ![![-1581261221903263543036142220635597, 351034497426941009626707179226787, -151265042722381294844644123463647]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3626064788809, 160184602912, -102941839404]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![3626064788809, 160184602912, -102941839404]] 
 ![![41, 0, 0], ![0, 41, 0], ![24, 26, 1]] where
  M :=![![![3626064788809, 160184602912, -102941839404], ![13176555443712, 2013150746629, 709524862768], ![-7327073729024, 2997332704880, 2722675609397]]]
  hmulB := by decide  
  f := ![![![81816447799661411574753, -18162967153550242630624, 7826643884248989891452]], ![![-1001810417183870706105856, 222398431987051028272597, -95834194537855738848560]], ![![-555132359051663515374248, 123237454992148301568738, -53104521153977516176675]]]
  g := ![![![148699242305, 69187132376, -102941839404], ![-93952225920, -400841358179, 709524862768], ![-1772470447672, -1653469100962, 2722675609397]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [18, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 40], [0, 1]]
 g := ![![[2, 16], [31], [40], [27, 25], [1]], ![[0, 25], [31], [40], [29, 16], [1]]]
 h' := ![![[5, 40], [21, 4], [13, 21], [6, 9], [23, 5], [0, 1]], ![[0, 1], [0, 37], [36, 20], [10, 32], [7, 36], [5, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [6, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [18, 36, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1425, -2907, 1924]
  a := ![-1, -5, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1161, -1291, 1924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81816447799661411574753, 18162967153550242630624, -7826643884248989891452]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-81816447799661411574753, 18162967153550242630624, -7826643884248989891452]] 
 ![![41, 0, 0], ![19, 1, 0], ![21, 0, 1]] where
  M :=![![![-81816447799661411574753, 18162967153550242630624, -7826643884248989891452], ![1001810417183870706105856, -222398431987051028272597, 95834194537855738848560], ![-1323049378470560350614016, 293712365300040547634288, -126564237449195289424037]]]
  hmulB := by decide  
  f := ![![![-3626064788809, -160184602912, 102941839404]], ![![-2001750888563, -123333126877, 30399270388]], ![![-1678543581365, -155151447952, -13680414193]]]
  g := ![![![-6403739076777737410637, 18162967153550242630624, -7826643884248989891452], ![78411281454704139694279, -222398431987051028272597, 95834194537855738848560], ![-103554520310688528725871, 293712365300040547634288, -126564237449195289424037]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![3626064788809, 160184602912, -102941839404]] ![![-81816447799661411574753, 18162967153550242630624, -7826643884248989891452]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107943818785173015071195715, 23963152737022038900071109, -10326014534463226561778815]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-107943818785173015071195715, 23963152737022038900071109, -10326014534463226561778815]] 
 ![![43, 0, 0], ![0, 43, 0], ![16, 29, 1]] where
  M :=![![![-107943818785173015071195715, 23963152737022038900071109, -10326014534463226561778815], ![1321729860411292999907688320, -293419436875334623950976007, 126438011021301366053382503], ![-1745553689927527979301413632, 387506854520801146642127979, -166981425854033257897593504]]]
  hmulB := by decide  
  f := ![![![18662172611463, 1046361499743, -361752802654]], ![![46304358739712, 11543807283040, 5877519287585]], ![![36134680279248, 8543330356583, 4234449792282]]]
  g := ![![![1331916599214851393424775, 7521338935731525795154808, -10326014534463226561778815], ![-16308798044872764115033296, -92095854802164517197652758, 126438011021301366053382503], ![21538351714814049931629824, 121627167541575944783077665, -166981425854033257897593504]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [19, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 42], [0, 1]]
 g := ![![[32, 21], [24, 16], [21], [12, 36], [1]], ![[35, 22], [14, 27], [21], [11, 7], [1]]]
 h' := ![![[37, 42], [17, 35], [28, 39], [30, 35], [24, 37], [0, 1]], ![[0, 1], [22, 8], [9, 4], [35, 8], [17, 6], [37, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [41, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [19, 6, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3731, -217, 295]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23, -204, 295]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18662172611463, 1046361499743, -361752802654]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![18662172611463, 1046361499743, -361752802654]] 
 ![![43, 0, 0], ![8, 1, 0], ![25, 0, 1]] where
  M :=![![![18662172611463, 1046361499743, -361752802654], ![46304358739712, 11543807283040, 5877519287585], ![-87629913227392, 15851010129021, 17421326570625]]]
  hmulB := by decide  
  f := ![![![-107943818785173015071195715, 23963152737022038900071109, -10326014534463226561778815]], ![![10655332793718811147398200, -2365446859980425877916445, 1019299877804547757189581]], ![![-103352306036205892001890849, 22943852859217491142881528, -9886785795711951673071253]]]
  g := ![![![449653504183, 1046361499743, -361752802654], ![-4488001900331, 11543807283040, 5877519287585], ![-15115608337795, 15851010129021, 17421326570625]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-107943818785173015071195715, 23963152737022038900071109, -10326014534463226561778815]] ![![18662172611463, 1046361499743, -361752802654]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1771682101, -393307271, 169480896]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1771682101, -393307271, 169480896]] 
 ![![47, 0, 0], ![0, 47, 0], ![33, 18, 1]] where
  M :=![![![1771682101, -393307271, 169480896], ![-21693554688, 4815893770, -2075227313], ![28649776000, -6360150733, 2740666457]]]
  hmulB := by decide  
  f := ![![![-91437, 257, 5849]], ![![-748672, -27869, 25195]], ![![-367555, -11926, 13699]]]
  g := ![![![-81301861, -73275817, 169480896], ![995509503, 897233732, -2075227313], ![-1314728023, -1184939297, 2740666457]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [24, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 46], [0, 1]]
 g := ![![[16, 2], [29, 28], [5, 7], [13, 17], [1]], ![[0, 45], [40, 19], [43, 40], [18, 30], [1]]]
 h' := ![![[39, 46], [9, 7], [21, 34], [17, 17], [23, 39], [0, 1]], ![[0, 1], [0, 40], [31, 13], [22, 30], [40, 8], [39, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [12, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [24, 8, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4063, -5613, 3127]
  a := ![1, 7, -16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2282, -1317, 3127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91437, -257, -5849]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![91437, -257, -5849]] 
 ![![47, 0, 0], ![11, 1, 0], ![21, 0, 1]] where
  M :=![![![91437, -257, -5849], ![748672, 27869, -25195], ![781568, 67361, 2674]]]
  hmulB := by decide  
  f := ![![![-1771682101, 393307271, -169480896]], ![![46915991, -10415187, 4488031]], ![![-1401172343, 311055392, -134037559]]]
  g := ![![![4619, -257, -5849], ![20664, 27869, -25195], ![-331, 67361, 2674]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1771682101, -393307271, 169480896]] ![![91437, -257, -5849]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18697, 2159, 2791]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-18697, 2159, 2791]] 
 ![![53, 0, 0], ![0, 53, 0], ![17, 42, 1]] where
  M :=![![![-18697, 2159, 2791], ![-357248, 5527, 26277], ![-633600, -9743, 31804]]]
  hmulB := by decide  
  f := ![![![8147123, -1808633, 779362]], ![![-99758336, 22146004, -9542983]], ![![-73954761, 16417700, -7074587]]]
  g := ![![![-1248, -2171, 2791], ![-15169, -20719, 26277], ![-22156, -25387, 31804]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [50, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 52], [0, 1]]
 g := ![![[42, 17], [4], [4, 49], [17], [20, 1]], ![[11, 36], [4], [30, 4], [17], [40, 52]]]
 h' := ![![[20, 52], [50, 32], [12, 51], [47, 46], [7, 32], [0, 1]], ![[0, 1], [1, 21], [25, 2], [13, 7], [11, 21], [20, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [16, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [50, 33, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3022, -2958, 1459]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-525, -1212, 1459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8147123, 1808633, -779362]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-8147123, 1808633, -779362]] 
 ![![53, 0, 0], ![20, 1, 0], ![12, 0, 1]] where
  M :=![![![-8147123, 1808633, -779362], ![99758336, -22146004, 9542983], ![-131746688, 29247307, -12603021]]]
  hmulB := by decide  
  f := ![![![18697, -2159, -2791]], ![![13796, -919, -1549]], ![![16188, -305, -1232]]]
  g := ![![![-659763, 1808633, -779362], ![8078540, -22146004, 9542983], ![-10668992, 29247307, -12603021]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-18697, 2159, 2791]] ![![-8147123, 1808633, -779362]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2585044078500127401, 573870804110755771, -247287922803106794]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-2585044078500127401, 573870804110755771, -247287922803106794]] 
 ![![59, 0, 0], ![2, 1, 0], ![34, 0, 1]] where
  M :=![![![-2585044078500127401, 573870804110755771, -247287922803106794], ![31652854118797669632, -7026823641666569448, 3027943937562863221], ![-41802608807379069056, 9280033918855595009, -3998879704103706227]]]
  hmulB := by decide  
  f := ![![![-27848288707, -488494871, 1352231321]], ![![-3877664178, -211614395, 79558031]], ![![-17922035282, -647610933, 617916382]]]
  g := ![![![79237350653965967, 573870804110755771, -247287922803106794], ![-970230380932314254, -7026823641666569448, 3027943937562863221], ![1281342937193826316, 9280033918855595009, -3998879704103706227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107829671879, 6665236633, -1621207238]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![107829671879, 6665236633, -1621207238]] 
 ![![59, 0, 0], ![18, 1, 0], ![12, 0, 1]] where
  M :=![![![107829671879, 6665236633, -1621207238], ![207514526464, 70000682362, 40171827479], ![-645635762560, 92772089819, 110172509841]]]
  hmulB := by decide  
  f := ![![![3985326479328999788141, -884728632040735115275, 381240349037800174363]], ![![388764609340399557086, -86304392574003813949, 37189614483838271679]], ![![1902888440276672371092, -422434622464245927859, 182032226698079051438]]]
  g := ![![![123896599, 6665236633, -1621207238], ![-26009486200, 70000682362, 40171827479], ![-61654296566, 92772089819, 110172509841]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, -65, 28]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![293, -65, 28]] 
 ![![59, 0, 0], ![38, 1, 0], ![46, 0, 1]] where
  M :=![![![293, -65, 28], ![-3584, 796, -343], ![4736, -1051, 453]]]
  hmulB := by decide  
  f := ![![![95, 17, 7]], ![![46, 13, 7]], ![![22, 15, 10]]]
  g := ![![![25, -65, 28], ![-306, 796, -343], ![404, -1051, 453]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-2585044078500127401, 573870804110755771, -247287922803106794]] ![![107829671879, 6665236633, -1621207238]]
  ![![-95, -17, -7]] where
 M := ![![![-95, -17, -7]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-95, -17, -7]] ![![293, -65, 28]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [47, 42, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 47, 2], [34, 13, 59], [0, 1]]
 g := ![![[10, 54, 47], [4, 45], [48, 59, 5], [2, 27, 20], [1]], ![[3, 55, 39, 38], [36, 56], [22, 11, 55, 54], [15, 50, 0, 38], [2, 44, 4, 8]], ![[27, 43, 12, 30], [34, 15], [44, 53, 27, 53], [39, 25, 10, 6], [51, 57, 45, 53]]]
 h' := ![![[18, 47, 2], [57, 16, 13], [1, 21, 17], [28, 2, 26], [14, 19, 52], [0, 1]], ![[34, 13, 59], [13, 20, 18], [34, 11, 19], [10, 33, 37], [4, 39, 43], [18, 47, 2]], ![[0, 1], [40, 25, 30], [33, 29, 25], [11, 26, 59], [2, 3, 27], [34, 13, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 11], []]
 b := ![[], [23, 47, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [47, 42, 9, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1844759011, -493290103, 131686129]
  a := ![1, -41, 102]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30241951, -8086723, 2158789]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [35, 2, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 40, 59], [22, 26, 8], [0, 1]]
 g := ![![[14, 50, 59], [2, 53, 10], [41, 37], [8, 1], [1, 1], []], ![[60, 52, 27, 37], [65, 50, 33, 9], [48, 47], [64, 4], [53, 6], [27, 64]], ![[1, 15, 8, 28], [4, 34, 32, 5], [41, 33], [24, 1], [64, 59], [11, 64]]]
 h' := ![![[46, 40, 59], [64, 56, 40], [21, 66, 12], [7, 60, 38], [32, 30, 66], [0, 0, 1], [0, 1]], ![[22, 26, 8], [34, 60, 56], [24, 43, 52], [30, 61, 39], [40, 15, 2], [32, 46, 26], [46, 40, 59]], ![[0, 1], [30, 18, 38], [48, 25, 3], [64, 13, 57], [57, 22, 66], [32, 21, 40], [22, 26, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 49], []]
 b := ![[], [61, 36, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [35, 2, 66, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![693986, -312354, 110148]
  a := ![-1, -3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10358, -4662, 1644]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [18, 3, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 45, 26], [67, 25, 45], [0, 1]]
 g := ![![[28, 58, 27], [38, 13, 16], [39, 21, 50], [44, 8], [60, 1], []], ![[3, 13, 64, 41], [59, 26, 12, 17], [63, 35, 40, 26], [36, 9], [49, 57], [16, 37]], ![[65, 59, 14, 12], [19, 32, 4, 32], [62, 1, 63, 19], [35, 15], [66, 37], [68, 37]]]
 h' := ![![[64, 45, 26], [26, 0, 13], [8, 3, 67], [1, 55, 11], [56, 15, 47], [0, 0, 1], [0, 1]], ![[67, 25, 45], [43, 65, 41], [20, 44, 49], [40, 45, 1], [7, 58, 3], [45, 5, 25], [64, 45, 26]], ![[0, 1], [13, 6, 17], [0, 24, 26], [54, 42, 59], [20, 69, 21], [70, 66, 45], [67, 25, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 68], []]
 b := ![[], [61, 14, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [18, 3, 11, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12511762, -3329900, 930881]
  a := ![0, -8, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![176222, -46900, 13111]
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


def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![447058432965767299164784894011967, -99245418886402420742384823911914, 42766060423952306288284904954420]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![447058432965767299164784894011967, -99245418886402420742384823911914, 42766060423952306288284904954420]] 
 ![![73, 0, 0], ![46, 1, 0], ![72, 0, 1]] where
  M :=![![![447058432965767299164784894011967, -99245418886402420742384823911914, 42766060423952306288284904954420], ![-5474055734265895204900467834165760, 1215221354288449930563073320246329, -523653690509007720043554147565718], ![7229357883193614650124789626559232, -1604892332837854303625651922484094, 691567663779442210519519172680611]]]
  hmulB := by decide  
  f := ![![![336184164087537527, 17451428474703974, -7575205759159928]], ![![225124628564372562, 13743401714370537, -3515072447055734]], ![![314261689133055672, 21087274417949986, -3466479767952881]]]
  g := ![![![26482073304324830144629775852627, -99245418886402420742384823911914, 42766060423952306288284904954420], ![-324262634450493646132410163572126, 1215221354288449930563073320246329, -523653690509007720043554147565718], ![428240183583768129582183529148268, -1604892332837854303625651922484094, 691567663779442210519519172680611]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, -14, 6]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![63, -14, 6]] 
 ![![73, 0, 0], ![53, 1, 0], ![49, 0, 1]] where
  M :=![![![63, -14, 6], ![-768, 171, -74], ![1024, -226, 97]]]
  hmulB := by decide  
  f := ![![![-137, 2, 10]], ![![-117, 1, 8]], ![![-113, 0, 7]]]
  g := ![![![7, -14, 6], ![-85, 171, -74], ![113, -226, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![447058432965767299164784894011967, -99245418886402420742384823911914, 42766060423952306288284904954420]] ![![447058432965767299164784894011967, -99245418886402420742384823911914, 42766060423952306288284904954420]]
  ![![1052307352899573464009680765149646847771273310407865275253444279169, -233608576272526141871524846912751155166286409365512436012992734024, 100664782319671597157706448182459663457378072975890008796400459012]] where
 M := ![![![1052307352899573464009680765149646847771273310407865275253444279169, -233608576272526141871524846912751155166286409365512436012992734024, 100664782319671597157706448182459663457378072975890008796400459012]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI73N1 : IdealMulLeCertificate' Table 
  ![![1052307352899573464009680765149646847771273310407865275253444279169, -233608576272526141871524846912751155166286409365512436012992734024, 100664782319671597157706448182459663457378072975890008796400459012]] ![![63, -14, 6]]
  ![![73, 0, 0]] where
 M := ![![![348787486905316920679432373572259333957653327675720432206459479346367, -77429610287441779713807936823411387343600246839763882399756481163182, 33365362646572520206848448736140053924298507234156442769732972516954]]]
 hmul := by decide  
 g := ![![![![4777910779524889324375785939346018273392511338023567564472047662279, -1060679592978654516627505983882347771830140367667998389037760015934, 457059762281815345299293818303288409921897359372006065338807842698]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![246316312827, 3670615355, -12452645622]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![246316312827, 3670615355, -12452645622]] 
 ![![79, 0, 0], ![31, 1, 0], ![34, 0, 1]] where
  M :=![![![246316312827, 3670615355, -12452645622], ![1593938639616, 98325364920, -24116275003], ![1124099874176, 189808516369, 74209089917]]]
  hmulB := by decide  
  f := ![![![-11874110225136348535747, 2636011215310659062053, -1135889355671175909175]], ![![-2819032651307801116883, 625815454318723673428, -269671505586285359326]], ![![-7540953742892274604858, 1674065531101693274715, -721375237870649770090]]]
  g := ![![![7036926430, 3670615355, -12452645622], ![-8027776238, 98325364920, -24116275003], ![-92190799879, 189808516369, 74209089917]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![417425749, -92667066, 39931368]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![417425749, -92667066, 39931368]] 
 ![![79, 0, 0], ![55, 1, 0], ![9, 0, 1]] where
  M :=![![![417425749, -92667066, 39931368], ![-5111215104, 1134671995, -488943990], ![6750169344, -1498514142, 645728005]]]
  hmulB := by decide  
  f := ![![![-186605, -22926, -5820]], ![![-120485, -18263, -6378]], ![![25317, -4920, -5291]]]
  g := ![![![65249773, -92667066, 39931368], ![-798957961, 1134671995, -488943990], ![1055150571, -1498514142, 645728005]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5402662258615, 1199372250739, -516824118649]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-5402662258615, 1199372250739, -516824118649]] 
 ![![79, 0, 0], ![71, 1, 0], ![10, 0, 1]] where
  M :=![![![-5402662258615, 1199372250739, -516824118649], ![66153487187072, -14685844315971, 6328309280577], ![-87366160907520, 19394984181917, -8357535035394]]]
  hmulB := by decide  
  f := ![![![-41751465, 613967, 3046776]], ![![-42460017, 424213, 2946911]], ![![-11216326, -299595, 466757]]]
  g := ![![![-1080884188286, 1199372250739, -516824118649], ![13235004314117, -14685844315971, 6328309280577], ![-17478920094553, 19394984181917, -8357535035394]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![246316312827, 3670615355, -12452645622]] ![![417425749, -92667066, 39931368]]
  ![![-41751465, 613967, 3046776]] where
 M := ![![![-41751465, 613967, 3046776]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-41751465, 613967, 3046776]] ![![-5402662258615, 1199372250739, -516824118649]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB169I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB169I1 : PrimesBelowBoundCertificateInterval O 31 79 169 where
  m := 11
  g := ![2, 2, 2, 2, 2, 3, 1, 1, 1, 3, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB169I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![357911]
    · exact ![73, 73, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
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
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N1, I41N1, I43N1, I47N1, I53N1, I59N0, I59N1, I59N2, I73N0, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [], [], [], [I73N0, I73N0, I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
