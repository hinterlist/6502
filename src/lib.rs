type Byte = u8; // 8-bit value
type Word = u16; // 16-bit value

/// CPU Instructions
///
/// Instruction reference:
/// https://www.nesdev.org/obelisk-6502-guide/reference.html
///
// ADC - Add with Carry
// const INS_ADC_IM: Byte = 0x69;
// const INS_ADC_ZP: Byte = 0x65;
// const INS_ADC_ZPX: Byte = 0x75;
// const INS_ADC_A: Byte = 0x6D;
// const INS_ADC_AX: Byte = 0x7D;
// const INS_ADC_AY: Byte = 0x79;
// const INS_ADC_IX: Byte = 0x61;
// const INS_ADC_IY: Byte = 0x71;
// LDA - Load Accumulator
const INS_LDA_IM: Byte = 0xA9;
const INS_LDA_ZP: Byte = 0xA5;
const INS_LDA_ZPX: Byte = 0xB5;
const INS_LDA_A: Byte = 0xAD;
const INS_LDA_AX: Byte = 0xBD;
const INS_LDA_AY: Byte = 0xB9;
const INS_LDA_IX: Byte = 0xA1;
const INS_LDA_IY: Byte = 0xB1;
// LDX - Load X Register
const INS_LDX_IM: Byte = 0xA2;
const INS_LDX_ZP: Byte = 0xA6;
const INS_LDX_ZPY: Byte = 0xB6;
const INS_LDX_A: Byte = 0xAE;
const INS_LDX_AY: Byte = 0xBE;
// LDY - Load Y Register
const INS_LDY_IM: Byte = 0xA0;
const INS_LDY_LZ: Byte = 0xA4;
const INS_LDY_LZX: Byte = 0xB4;
const INS_LDY_A: Byte = 0xAC;
const INS_LDY_AX: Byte = 0xBC;

#[derive(Default)]
pub struct Cpu {
    pc: Word, // Program counter register
    sp: Word, // Stack pointer register
    a: Byte,  // Accumulator
    x: Byte,  // Index register X
    y: Byte,  // Index register Y

    // Processor status
    c: bool, // Carry Flag - The carry flag is set if the last operation caused an overflow from bit 7 of the result or an underflow from bit 0. This condition is set during arithmetic, comparison and during logical shifts. It can be explicitly set using the ‘Set Carry Flag’ (SEC) instruction and cleared with ‘Clear Carry Flag’ (CLC).
    z: bool, // Zero Flag - The zero flag is set if the result of the last operation as was zero.
    i: bool, // Interrupt Disable - The interrupt disable flag is set if the program has executed a ‘Set Interrupt Disable’ (SEI) instruction. While this flag is set the processor will not respond to interrupts from devices until it is cleared by a ‘Clear Interrupt Disable’ (CLI) instruction.
    d: bool, // Decimal Mode - While the decimal mode flag is set the processor will obey the rules of Binary Coded Decimal (BCD) arithmetic during addition and subtraction. The flag can be explicitly set using ‘Set Decimal Flag’ (SED) and cleared with ‘Clear Decimal Flag’ (CLD).
    b: bool, // Break Command - The break command bit is set when a BRK instruction has been executed and an interrupt has been generated to process it.
    v: bool, // Overflow Flag - The overflow flag is set during arithmetic operations if the result has yielded an invalid 2’s complement result (e.g. adding to positive numbers and ending up with a negative result: 64 + 64 => -128). It is determined by looking at the carry between bits 6 and 7 and between bit 7 and the carry flag.
    n: bool, // Negative Flag - The negative flag is set if the result of the last operation had bit 7 set to a one.
}

impl Cpu {
    pub fn new() -> Self {
        Cpu::default()
    }

    pub fn reset(&mut self, memory: &mut Mem) {
        self.pc = 0xFFFC;
        self.sp = 0x0100;

        // clear all flags
        self.c = false;
        self.z = false;
        self.i = false;
        self.d = false;
        self.b = false;
        self.v = false;
        self.n = false;

        // clear all registers
        self.a = 0;
        self.x = 0;
        self.y = 0;

        // Initialize memory
        memory.init();
    }

    /// fetch one byte from memory using address from PC register and increase program counter
    pub fn fetch_byte(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let data = memory.read_byte(self.pc);
        self.pc += 1;
        *cycles -= 1;

        data
    }

    /// fetch one two bytes from memory using address from PC register and increase program counter
    pub fn fetch_word(&mut self, cycles: &mut u32, memory: &mut Mem) -> Word {
        let data = memory.read_word(self.pc);
        self.pc += 2;
        *cycles -= 1;

        data
    }

    /// fetch one byte from memory from specified address
    fn read_byte(&mut self, cycles: &mut u32, addr: Word, memory: &mut Mem) -> Byte {
        let data = memory.read_byte(addr);
        *cycles -= 1;

        data
    }

    fn read_word(&mut self, cycles: &mut u32, addr: Word, memory: &mut Mem) -> Word {
        let data = memory.read_word(addr);
        *cycles -= 2;

        data
    }

    /// Add two bytes ignoring overflow
    fn overflowing_add(&mut self, cycles: &mut u32, a: Byte, b: Byte) -> (Byte, bool) {
        let (data, overflow) = a.overflowing_add(b);
        *cycles -= 1;

        (data, overflow)
    }

    /// Addressing Modes

    /// Immediate addressing allows the programmer to directly specify an 8 bit constant within the instruction
    fn addr_immediate(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        self.fetch_byte(cycles, memory)
    }

    /// An instruction using zero page addressing mode has only an 8 bit address operand. This limits it to addressing
    /// only the first 256 bytes of memory (e.g. $0000 to $00FF) where the most significant byte of the address is
    /// always zero. In zero page mode only the least significant byte of the address is held in the instruction making
    /// it shorter by one byte (important for space saving) and one less memory fetch during execution (important for speed).
    fn addr_zero_page(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let addr = self.fetch_byte(cycles, memory) as Word;
        self.read_byte(cycles, addr, memory)
    }

    /// The address to be accessed by an instruction using indexed zero page addressing is calculated by taking the 8 bit
    /// zero page address from the instruction and adding the current value of the X register to it. For example if the X
    /// register contains $0F and the instruction LDA $80,X is executed then the accumulator will be loaded from $008F
    /// (e.g. $80 + $0F => $8F).
    ///
    /// NB:
    /// The address calculation wraps around if the sum of the base address and the register exceed $FF. If we repeat the
    /// last example but with $FF in the X register then the accumulator will be loaded from $007F (e.g. $80 + $FF => $7F)
    /// and not $017F.
    fn addr_zero_page_x(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let addr = self.fetch_byte(cycles, memory);
        let (addr, _) = self.overflowing_add(cycles, addr, self.x);
        self.read_byte(cycles, addr as Word, memory)
    }

    /// The address to be accessed by an instruction using indexed zero page addressing is calculated by taking the 8 bit
    /// zero page address from the instruction and adding the current value of the Y register to it. This mode can only be used with the LDX and STX instructions.
    fn addr_zero_page_y(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let addr = self.fetch_byte(cycles, memory);
        let (addr, _) = self.overflowing_add(cycles, addr, self.y);
        self.read_byte(cycles, addr as Word, memory)
    }

    /// Instructions using absolute addressing contain a full 16 bit address to identify the target location.
    fn addr_absolute(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let addr = self.fetch_byte(cycles, memory) as Word;
        let addr = addr << 8;
        let addr = addr | (self.fetch_byte(cycles, memory) as Word);

        self.read_byte(cycles, addr, memory)
    }

    /// The address to be accessed by an instruction using X register indexed absolute addressing is computed by
    /// taking the 16 bit address from the instruction and added the contents of the X register. For example if X
    /// contains $92 then an STA $2000,X instruction will store the accumulator at $2092 (e.g. $2000 + $92).
    fn addr_absolute_x(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let addr = self.fetch_word(cycles, memory);
        let addr = addr | (self.x as Word);

        self.read_byte(cycles, addr, memory)
    }

    /// The Y register indexed absolute addressing mode is the same as the previous mode only with the contents
    /// of the Y register added to the 16 bit address from the instruction.
    fn addr_absolute_y(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let addr = self.fetch_word(cycles, memory);
        let addr = addr | (self.y as Word);

        self.read_byte(cycles, addr, memory)
    }

    /// Indexed indirect addressing is normally used in conjunction with a table of address held on zero page.
    /// The address of the table is taken from the instruction and the X register added to it (with zero page wrap around)
    /// to give the location of the least significant byte of the target address.
    fn addr_indirect_x(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let addr = self.fetch_byte(cycles, memory);
        let addr = (addr + self.x) as Word;
        *cycles -= 1;

        let target_addr = self.read_word(cycles, addr, memory);

        self.read_byte(cycles, target_addr, memory)
    }

    /// In instruction contains the zero page location of the least significant byte of 16 bit address.
    /// The Y register is dynamically added to this value to generated the actual target address for operation.
    fn addr_indirect_y(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let addr = self.fetch_byte(cycles, memory) as Word;
        let target_addr = self.read_byte(cycles, addr, memory) as Word;
        let target_addr = target_addr << 8;
        let target_addr = target_addr | self.read_byte(cycles, addr + 1, memory) as Word;
        let target_addr = target_addr + (self.y as Word);

        self.read_byte(cycles, target_addr, memory)
    }

    /// Execute instructions for next X cycles
    pub fn exec(&mut self, cycles: u32, memory: &mut Mem) -> u32 {
        let mut cycles = cycles;

        while cycles > 0 {
            let instruction = self.fetch_byte(&mut cycles, memory);

            match instruction {
                // INS_ADC_IM => {
                //     let value = self.addr_immediate(&mut cycles, memory);
                //     let (result, overflow) = self.overflowing_add(&mut cycles, self.a, value);
                //     self.a = result;

                //     self.adc_status(overflow);
                // }
                // LDA - Load Accumulator
                INS_LDA_IM => {
                    self.a = self.addr_immediate(&mut cycles, memory);
                    self.ld_status(self.a);
                }
                INS_LDA_ZP => {
                    self.a = self.addr_zero_page(&mut cycles, memory);
                    self.ld_status(self.a);
                }
                INS_LDA_ZPX => {
                    self.a = self.addr_zero_page_x(&mut cycles, memory);
                    self.ld_status(self.a);
                }
                INS_LDA_A => {
                    self.a = self.addr_absolute(&mut cycles, memory);
                    self.ld_status(self.a);
                }
                INS_LDA_AX => {
                    self.a = self.addr_absolute_x(&mut cycles, memory);
                    self.ld_status(self.a);
                }
                INS_LDA_AY => {
                    self.a = self.addr_absolute_y(&mut cycles, memory);
                    self.ld_status(self.a);
                }
                INS_LDA_IX => {
                    self.a = self.addr_indirect_x(&mut cycles, memory);
                    self.ld_status(self.a);
                }
                INS_LDA_IY => {
                    self.a = self.addr_indirect_y(&mut cycles, memory);
                    self.ld_status(self.a);
                }
                // LDX - Load X Register
                INS_LDX_IM => {
                    self.x = self.addr_immediate(&mut cycles, memory);
                    self.ld_status(self.x)
                }
                INS_LDX_ZP => {
                    self.x = self.addr_zero_page(&mut cycles, memory);
                    self.ld_status(self.x)
                }
                INS_LDX_ZPY => {
                    self.x = self.addr_zero_page_y(&mut cycles, memory);
                    self.ld_status(self.x);
                }
                INS_LDX_A => {
                    self.x = self.addr_absolute(&mut cycles, memory);
                    self.ld_status(self.x)
                }
                INS_LDX_AY => {
                    self.x = self.addr_absolute_y(&mut cycles, memory);
                    self.ld_status(self.x);
                }
                // LDY - Load Y Register
                INS_LDY_IM => {
                    self.y = self.addr_immediate(&mut cycles, memory);
                    self.ld_status(self.y)
                }
                INS_LDY_LZ => {
                    self.y = self.addr_zero_page(&mut cycles, memory);
                    self.ld_status(self.y)
                }
                INS_LDY_LZX => {
                    self.y = self.addr_zero_page_x(&mut cycles, memory);
                    self.ld_status(self.y);
                }
                INS_LDY_A => {
                    self.y = self.addr_absolute(&mut cycles, memory);
                    self.ld_status(self.y)
                }
                INS_LDY_AX => {
                    self.y = self.addr_absolute_x(&mut cycles, memory);
                    self.ld_status(self.y);
                }
                _ => {
                    unreachable!()
                }
            };
        }

        cycles
    }

    /// Update status flags after ADC instruction
    // fn adc_status(&mut self, overflow: bool) {
    //     self.z = self.a == 0;
    //     self.n = (self.a << 7) > 0;
    //     self.c = overflow;
    // }

    /// Update status flags after LDA, LDX, LDY instruction(s)
    fn ld_status(&mut self, value: Byte) {
        self.z = value == 0;
        self.n = (value << 7) > 0;
    }
}

const MAX_MEM: usize = 1024 * 64; // 64kb of memory

pub struct Mem([Byte; MAX_MEM]);

impl Default for Mem {
    fn default() -> Self {
        Mem([0; MAX_MEM])
    }
}

impl Mem {
    pub fn new() -> Self {
        Mem::default()
    }

    pub fn init(&mut self) {
        for i in 0..MAX_MEM {
            self.0[i] = 0;
        }
    }

    pub fn read_byte(&self, addr: Word) -> Byte {
        self.0[addr as usize]
    }

    pub fn read_word(&self, addr: Word) -> Word {
        ((self.0[addr as usize] as Word) << 8) | (self.0[(addr + 1) as usize] as Word)
    }

    pub fn write_byte(&mut self, addr: Word, value: Byte) {
        self.0[addr as usize] = value;
    }
}

#[cfg(test)]
mod tests {
    use std::mem;

    use super::*;

    fn init() -> (Cpu, Mem) {
        let mut memory = Mem::new();
        let mut cpu = Cpu::new();
        cpu.reset(&mut memory);

        (cpu, memory)
    }

    // #[test]
    // // fn inst_adc_im() {
    // //     let (mut cpu, mut memory) = init();

    // //     memory.write_byte(0xFFFC, INS_ADC_IM);
    // //     memory.write_byte(0xFFFD, 0x02);
    // //     cpu.a = 0xFF;
    // //     cpu.exec(2, &mut memory);

    // //     assert_eq!(cpu.a, 0x01);
    // //     assert!(cpu.c);
    // // }

    #[test]
    fn inst_lda_im() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_IM);
        memory.write_byte(0xFFFD, 0x0F);

        let cycles = cpu.exec(2, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_lda_zp() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_ZP);
        memory.write_byte(0xFFFD, 0x01);
        memory.write_byte(0x0001, 0x0F);

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_lda_zpx() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_ZPX);
        memory.write_byte(0xFFFD, 0x01);
        memory.write_byte(0x02, 0x0F);
        cpu.x = 0x01;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_lda_zpx_overflow() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_ZPX);
        memory.write_byte(0xFFFD, 0xFF);
        memory.write_byte(0x7F, 0x0F);
        cpu.x = 0x80;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_lda_a() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_A);
        memory.write_byte(0xFFFD, 0x12);
        memory.write_byte(0xFFFE, 0x34);
        memory.write_byte(0x1234, 0x0F);

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_lda_ax() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_AX);
        memory.write_byte(0xFFFD, 0x12);
        memory.write_byte(0xFFFE, 0x34);
        memory.write_byte(0x1235, 0x0F);
        cpu.x = 0x01;

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_lda_ay() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_AY);
        memory.write_byte(0xFFFD, 0x12);
        memory.write_byte(0xFFFE, 0x34);
        memory.write_byte(0x1235, 0x0F);
        cpu.y = 0x01;

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_lda_ix() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_IX);
        memory.write_byte(0xFFFD, 0x12);
        cpu.x = 0x33;

        memory.write_byte(0x0045, 0x01);
        memory.write_byte(0x0046, 0x02);
        memory.write_byte(0x0102, 0x0F);

        let cycles = cpu.exec(6, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_lda_iy() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_IY);
        memory.write_byte(0xFFFD, 0x01);
        memory.write_byte(0x0001, 0x01);
        memory.write_byte(0x0002, 0x02);
        cpu.y = 0x03;

        memory.write_byte(0x0105, 0x0F);

        let cycles = cpu.exec(5, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_lda_zero_flag() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_IM);
        memory.write_byte(0xFFFD, 0x0);
        let cycles = cpu.exec(2, &mut memory);

        assert!(cpu.z);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_lda_negative_flag() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDA_IM);
        memory.write_byte(0xFFFD, 0xFF);
        let cycles = cpu.exec(2, &mut memory);

        assert!(cpu.n);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_ldx_im() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDX_IM);
        memory.write_byte(0xFFFD, 0x0F);
        let cycles = cpu.exec(2, &mut memory);

        assert_eq!(cpu.x, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_ldx_zp() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDX_ZP);
        memory.write_byte(0xFFFD, 0x01);
        memory.write_byte(0x0001, 0x0F);

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(cpu.x, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_ldx_zpy() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDX_ZPY);
        memory.write_byte(0xFFFD, 0x01);
        memory.write_byte(0x02, 0x0F);
        cpu.y = 0x01;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.x, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_ldx_a() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDX_A);
        memory.write_byte(0xFFFD, 0x12);
        memory.write_byte(0xFFFE, 0x34);
        memory.write_byte(0x1234, 0x0F);

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.x, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_ldx_ay() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDX_AY);
        memory.write_byte(0xFFFD, 0x12);
        memory.write_byte(0xFFFE, 0x34);
        memory.write_byte(0x1235, 0x0F);
        cpu.y = 0x01;

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(cpu.x, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_ldy_im() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDY_IM);
        memory.write_byte(0xFFFD, 0x0F);
        let cycles = cpu.exec(2, &mut memory);

        assert_eq!(cpu.y, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_ldy_lz() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDY_LZ);
        memory.write_byte(0xFFFD, 0x01);
        memory.write_byte(0x0001, 0x0F);

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(cpu.y, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_ldy_lzx() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDY_LZX);
        memory.write_byte(0xFFFD, 0x01);
        memory.write_byte(0x02, 0x0F);
        cpu.x = 0x01;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.y, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_ldy_a() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDY_A);
        memory.write_byte(0xFFFD, 0x12);
        memory.write_byte(0xFFFE, 0x34);
        memory.write_byte(0x1234, 0x0F);

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.y, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn ins_ldy_ax() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(0xFFFC, INS_LDY_AX);
        memory.write_byte(0xFFFD, 0x12);
        memory.write_byte(0xFFFE, 0x34);
        memory.write_byte(0x1235, 0x0F);
        cpu.x = 0x01;

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(cpu.y, 0x0F);
        assert_eq!(cycles, 0);
    }
}
