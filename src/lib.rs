use std::ops::BitOr;

type Byte = u8; // 8-bit value
type Word = u16; // 16-bit value

pub const RESET_VEC: Word = 0xFFFC;
pub const ENTRY_POINT: Word = 0x1000;

/// CPU Instructions
///
/// Instruction reference:
/// https://www.nesdev.org/obelisk-6502-guide/reference.html

// ADC - Add with Carry
const INST_ADC_IM: Byte = 0x69;
const INST_ADC_ZP: Byte = 0x65;
const INST_ADC_ZPX: Byte = 0x75;
const INST_ADC_A: Byte = 0x6D;
const INST_ADC_AX: Byte = 0x7D;
const INST_ADC_AY: Byte = 0x79;
const INST_ADC_IX: Byte = 0x61;
const INST_ADC_IY: Byte = 0x71;

// AND Memory with Accumulator
const INST_AND_IM: Byte = 0x29;
const INST_AND_ZP: Byte = 0x25;
const INST_AND_ZPX: Byte = 0x35;
const INST_AND_A: Byte = 0x2D;
const INST_AND_AX: Byte = 0x3D;
const INST_AND_AY: Byte = 0x39;
const INST_AND_IX: Byte = 0x21;
const INST_AND_IY: Byte = 0x31;

// ASL - Shift Left One Bit (Memory or Accumulator)
const INST_ASL_AC: Byte = 0x0A;
const INST_ASL_ZP: Byte = 0x06;
const INST_ASL_ZPX: Byte = 0x16;
const INST_ASL_A: Byte = 0x0E;
const INST_ASL_AX: Byte = 0x1E;

// BCC - Branch on Carry Clear
const INST_BCC: Byte = 0x90;

// LDA - Load Accumulator
const INST_LDA_IM: Byte = 0xA9;
const INST_LDA_ZP: Byte = 0xA5;
const INST_LDA_ZPX: Byte = 0xB5;
const INST_LDA_A: Byte = 0xAD;
const INST_LDA_AX: Byte = 0xBD;
const INST_LDA_AY: Byte = 0xB9;
const INST_LDA_IX: Byte = 0xA1;
const INST_LDA_IY: Byte = 0xB1;

// LDX - Load X Register
const INST_LDX_IM: Byte = 0xA2;
const INST_LDX_ZP: Byte = 0xA6;
const INST_LDX_ZPY: Byte = 0xB6;
const INST_LDX_A: Byte = 0xAE;
const INST_LDX_AY: Byte = 0xBE;

// LDY - Load Y Register
const INST_LDY_IM: Byte = 0xA0;
const INST_LDY_LZ: Byte = 0xA4;
const INST_LDY_LZX: Byte = 0xB4;
const INST_LDY_A: Byte = 0xAC;
const INST_LDY_AX: Byte = 0xBC;

// STA - Store Accumulator
const INST_STA_ZP: Byte = 0x85;
const INST_STA_ZPX: Byte = 0x95;
const INST_STA_A: Byte = 0x8D;
const INST_STA_AX: Byte = 0x9D;
const INST_STA_AY: Byte = 0x99;
const INST_STA_IX: Byte = 0x81;
const INST_STA_IY: Byte = 0x91;

#[derive(Default)]
pub struct Cpu {
    pc: Word, // Program counter register
    sp: Word, // Stack pointer register (256kb of stack start from 0x0100)
    a: Byte,  // Accumulator
    x: Byte,  // Index register X
    y: Byte,  // Index register Y

    // Processor status
    c: bool, // Carry Flag - The carry flag is set if the last operation caused an overflow from bit 7 of the result or an underflow from bit 0. This condition is set during arithmetic, comparison and during logical shifts. It can be explicitly set using the ‘Set Carry Flag’ (SEC) instruction and cleared with ‘Clear Carry Flag’ (CLC).
    z: bool, // Zero Flag - The zero flag is set if the result of the last operation was zero.
    i: bool, // Interrupt Disable - The interrupt disable flag is set if the program has executed a ‘Set Interrupt Disable’ (SEI) instruction. While this flag is set the processor will not respond to interrupts from devices until it is cleared by a ‘Clear Interrupt Disable’ (CLI) instruction.
    d: bool, // Decimal Mode - While the decimal mode flag is set the processor will obey the rules of Binary Coded Decimal (BCD) arithmetic during addition and subtraction. The flag can be explicitly set using ‘Set Decimal Flag’ (SED) and cleared with ‘Clear Decimal Flag’ (CLD).
    b: bool, // Break Command - The break command bit is set when a BRK instruction has been executed and an interrupt has been generated to process it.
    v: bool, // Overflow Flag - The overflow flag is set during arithmetic operations if the result has yielded an invalid 2’s complement result (e.g. adding to positive numbers and ending up with a negative result: 64 + 64 => -128). It is determined by looking at the carry between bits 6 and 7 and between bit 7 and the carry flag.
    n: bool, // Negative Flag - The negative flag is set if the result of the last operation had bit 7 set to a one.
}

#[repr(u8)]
enum UpdateStatusFlag {
    N = 0b0001,
    Z = 0b0010,
    C = 0b0100,
    V = 0b1000,
    All = 0b1111,
}

impl BitOr for UpdateStatusFlag {
    type Output = u8;

    fn bitor(self, rhs: Self) -> Self::Output {
        self as u8 | rhs as u8
    }
}

impl BitOr<UpdateStatusFlag> for u8 {
    type Output = u8;

    fn bitor(self, rhs: UpdateStatusFlag) -> Self::Output {
        self | rhs as u8
    }
}

impl Cpu {
    pub fn new() -> Self {
        Cpu::default()
    }

    /// Dump state of CPU
    ///
    /// Print out values of all registers, and status of flags.
    pub fn dump_registers(&self) {
        // Print state of register
        println!("State of registers:");
        println!(
            "  PC: {pc:#X}; SP: {sp:#X}; A: {a:#X}; X: {x:#X}; Y: {y:#X}",
            pc = self.pc,
            sp = self.sp,
            a = self.a,
            x = self.x,
            y = self.y
        );

        println!();

        // Print state of flags
        println!("State of flags:");
        println!("  Carry Flag.........: {}", self.c);
        println!("  Zero Flag..........: {}", self.z);
        println!("  Interrupt Disable..: {}", self.i);
        println!("  Decimal Mode.......: {}", self.d);
        println!("  Break Command......: {}", self.b);
        println!("  Overflow Flag......: {}", self.v);
        println!("  Negative Flag......: {}", self.n);
    }

    // Dump stack from current stack pointer, up to 0x0100
    pub fn dump_stack(&self, memory: &Mem) {
        println!("Stack:");
        if self.sp == 0x0100 {
            println!("  Stack is empty");
            return;
        }

        for addr in (self.sp..0x100).step_by(0x10) {
            let value = (addr..addr + 0x10)
                .map(|addr| format!("0x{:0>2X}", memory.read_byte(addr)))
                .collect::<Vec<_>>()
                .join(" ");

            println!("  0x{addr:0>2X}: {value}");
        }
    }

    pub fn reset(&mut self, memory: &mut Mem) {
        self.pc = 0x0000;
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

        // Set reset vector (the place where CPU will jump after reset)
        memory.write_byte(0xFFFC, (ENTRY_POINT << 8) as Byte);
        memory.write_byte(0xFFFD, (ENTRY_POINT >> 8) as Byte);
    }

    /// fetch one byte from memory using address from PC register and increase program counter
    pub fn fetch_byte(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let data = self.read_byte(cycles, self.pc, memory);
        self.pc += 1;

        data
    }

    /// fetch one byte from memory from specified address
    fn read_byte(&mut self, cycles: &mut u32, addr: Word, memory: &mut Mem) -> Byte {
        let data = memory.read_byte(addr);
        *cycles -= 1;

        data
    }

    // NOTE: not sure we gonna need that
    // /// store one byte in memory at address from PC register and increase program counter
    // pub fn store_byte(&mut self, cycles: &mut u32, memory: &mut Mem, value: Byte) {
    //     self.write_byte(cycles, memory, self.pc, value);
    //     self.pc += 1;
    // }

    /// fetch two bytes from memory using address from PC register and increase program counter
    pub fn fetch_word(&mut self, cycles: &mut u32, memory: &mut Mem) -> Word {
        let data = memory.read_word(self.pc);
        self.pc += 2;
        *cycles -= 1;

        data
    }

    /// write one byte to memory at specified address
    pub fn write_byte(&mut self, cycles: &mut u32, memory: &mut Mem, addr: Word, value: Byte) {
        memory.write_byte(addr, value);
        *cycles -= 1;
    }

    fn read_word(&mut self, cycles: &mut u32, addr: Word, memory: &mut Mem) -> Word {
        let data = memory.read_word(addr);
        *cycles -= 2;

        data
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
    fn addr_zero_page_read(&mut self, cycles: &mut u32, memory: &mut Mem) -> (Word, Byte) {
        let addr = self.fetch_byte(cycles, memory) as Word;
        let value = self.read_byte(cycles, addr, memory);

        (addr, value)
    }

    fn addr_zero_page_write(&mut self, cycles: &mut u32, memory: &mut Mem, value: Byte) {
        let addr = self.fetch_byte(cycles, memory) as Word;
        self.write_byte(cycles, memory, addr, value);
    }

    fn addr_zero_page(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        self.fetch_byte(cycles, memory)
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
    fn addr_zero_page_x(&mut self, cycles: &mut u32, memory: &mut Mem) -> Word {
        let addr = self.addr_zero_page(cycles, memory);
        let addr = addr.wrapping_add(self.x);

        *cycles -= 1;

        addr as Word
    }

    fn addr_zero_page_x_read(&mut self, cycles: &mut u32, memory: &mut Mem) -> (Word, Byte) {
        let addr = self.addr_zero_page_x(cycles, memory);
        let value = self.read_byte(cycles, addr, memory);

        (addr, value)
    }

    fn addr_zero_page_x_write(&mut self, cycles: &mut u32, memory: &mut Mem, value: Byte) {
        let addr = self.addr_zero_page_x(cycles, memory);
        self.write_byte(cycles, memory, addr, value);
    }

    fn addr_zero_page_y(&mut self, cycles: &mut u32, memory: &mut Mem) -> Word {
        let addr = self.addr_zero_page(cycles, memory);
        let addr = addr.wrapping_add(self.y);

        *cycles -= 1;

        addr as Word
    }

    /// The address to be accessed by an instruction using indexed zero page addressing is calculated by taking the 8 bit
    /// zero page address from the instruction and adding the current value of the Y register to it. This mode can only be used with the LDX and STX instructions.
    fn addr_zero_page_y_read(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        let addr = self.addr_zero_page_y(cycles, memory);
        self.read_byte(cycles, addr as Word, memory)
    }

    /// Instructions using absolute addressing contain a full 16 bit address to identify the target location.
    fn addr_absolute(&mut self, cycles: &mut u32, memory: &mut Mem) -> Word {
        let addr = self.fetch_byte(cycles, memory) as Word;
        let addr = addr << 8;
        let addr = addr | (self.fetch_byte(cycles, memory) as Word);

        addr as Word
    }

    /// The address to be accessed by an instruction using X register indexed absolute addressing is computed by
    /// taking the 16 bit address from the instruction and added the contents of the X register. For example if X
    /// contains $92 then an STA $2000,X instruction will store the accumulator at $2092 (e.g. $2000 + $92).
    fn addr_absolute_x(&mut self, cycles: &mut u32, memory: &mut Mem) -> Word {
        let addr = self.addr_absolute(cycles, memory);
        addr.wrapping_add(self.x as Word)
    }

    /// Read byte from memory referenced by address specified in next byte pointed by PC registry
    fn addr_absolute_read(&mut self, cycles: &mut u32, memory: &mut Mem) -> (Word, Byte) {
        let addr = self.addr_absolute(cycles, memory);
        let value = self.read_byte(cycles, addr, memory);

        (addr, value)
    }

    /// Write provided value to memory address referenced by address specified in next byte pointed by PC registry
    fn addr_absolute_write(&mut self, cycles: &mut u32, memory: &mut Mem, value: Byte) {
        let addr = self.addr_absolute(cycles, memory);
        self.write_byte(cycles, memory, addr, value);
    }

    fn addr_absolute_x_read(&mut self, cycles: &mut u32, memory: &mut Mem) -> (Word, Byte) {
        let addr = self.addr_absolute_x(cycles, memory);
        let value = self.read_byte(cycles, addr, memory);

        (addr, value)
    }

    /// Write provided value to memory address
    fn addr_absolute_x_write(&mut self, cycles: &mut u32, memory: &mut Mem, value: Byte) {
        let addr = self.addr_absolute_x(cycles, memory);
        self.write_byte(cycles, memory, addr, value);
    }

    fn addr_absolute_y(&mut self, cycles: &mut u32, memory: &mut Mem) -> Word {
        let addr = self.addr_absolute(cycles, memory);
        addr.wrapping_add(self.y as Word)
    }

    /// The Y register indexed absolute addressing mode is the same as the previous mode only with the contents
    /// of the Y register added to the 16 bit address from the instruction.
    fn addr_absolute_y_read(&mut self, cycles: &mut u32, memory: &mut Mem) -> (Word, Byte) {
        let addr = self.addr_absolute_y(cycles, memory);
        let value = self.read_byte(cycles, addr, memory);

        (addr, value)
    }

    fn addr_absolute_y_write(&mut self, cycles: &mut u32, memory: &mut Mem, value: Byte) {
        let addr = self.addr_absolute_y(cycles, memory);
        self.write_byte(cycles, memory, addr, value);
    }

    /// Indexed indirect addressing is normally used in conjunction with a table of address held on zero page.
    /// The address of the table is taken from the instruction and the X register added to it (with zero page wrap around)
    /// to give the location of the least significant byte of the target address.
    /// TODO: Replace with addr_zero_page
    fn addr_indirect(&mut self, cycles: &mut u32, memory: &mut Mem) -> Byte {
        self.fetch_byte(cycles, memory)
    }

    fn addr_indirect_x(&mut self, cycles: &mut u32, memory: &mut Mem) -> Word {
        let addr = self.addr_indirect(cycles, memory);
        let addr = addr.wrapping_add(self.x) as Word;

        *cycles -= 1;

        self.read_word(cycles, addr, memory)
    }

    fn addr_indirect_x_read(&mut self, cycles: &mut u32, memory: &mut Mem) -> (Word, Byte) {
        let addr = self.addr_indirect_x(cycles, memory) as Word;
        let value = self.read_byte(cycles, addr, memory);

        (addr, value)
    }

    fn addr_indirect_x_write(&mut self, cycles: &mut u32, memory: &mut Mem, value: Byte) {
        let addr = self.addr_indirect_x(cycles, memory);
        self.write_byte(cycles, memory, addr, value);
    }

    /// In instruction contains the zero page location of the least significant byte of 16 bit address.
    /// The Y register is dynamically added to this value to generated the actual target address for operation.
    fn addr_indirect_y(&mut self, cycles: &mut u32, memory: &mut Mem) -> Word {
        let addr = self.addr_indirect(cycles, memory) as Word;
        let target_addr = self.read_byte(cycles, addr, memory) as Word;
        let target_addr = target_addr << 8;
        let target_addr = target_addr | self.read_byte(cycles, addr + 1, memory) as Word;

        target_addr + (self.y as Word)
    }

    fn addr_indirect_y_read(&mut self, cycles: &mut u32, memory: &mut Mem) -> (Word, Byte) {
        let addr = self.addr_indirect_y(cycles, memory);
        let value = self.read_byte(cycles, addr, memory);

        (addr, value)
    }

    fn addr_indirect_y_write(&mut self, cycles: &mut u32, memory: &mut Mem, value: Byte) {
        let addr = self.addr_indirect_y(cycles, memory);
        self.write_byte(cycles, memory, addr, value);
    }

    /// Execute instructions for next X cycles
    pub fn exec(&mut self, cycles: u32, memory: &mut Mem) -> u32 {
        // Set program counter to reset vector
        let low_reset_vector = memory.read_byte(RESET_VEC) as Word;
        let high_reset_vector = memory.read_byte(RESET_VEC + 1) as Word;
        self.pc = (high_reset_vector << 8) | low_reset_vector;

        let mut cycles = cycles;

        while cycles > 0 {
            let instruction = self.fetch_byte(&mut cycles, memory);

            match instruction {
                // ADC - Add with Carry
                INST_ADC_IM => {
                    let value = self.addr_immediate(&mut cycles, memory);
                    let result = self.a as Word + value as Word + self.c as Word;

                    self.update_status_flags(UpdateStatusFlag::All as Byte, result, Some(value));
                    self.a = result as Byte;
                }
                INST_ADC_ZP => {
                    let (_, value) = self.addr_zero_page_read(&mut cycles, memory);
                    let result = self.a as Word + value as Word + self.c as Word;

                    self.update_status_flags(UpdateStatusFlag::All as Byte, result, Some(value));
                    self.a = result as Byte;
                }
                INST_ADC_ZPX => {
                    let (_, value) = self.addr_zero_page_x_read(&mut cycles, memory);
                    let result = self.a as Word + value as Word + self.c as Word;

                    self.update_status_flags(UpdateStatusFlag::All as Byte, result, Some(value));
                    self.a = result as Byte;
                }
                INST_ADC_A => {
                    let (_, value) = self.addr_absolute_read(&mut cycles, memory);
                    let result = self.a as Word + value as Word + self.c as Word;

                    self.update_status_flags(UpdateStatusFlag::All as Byte, result, Some(value));
                    self.a = result as Byte;
                }
                INST_ADC_AX => {
                    let (_, value) = self.addr_absolute_x_read(&mut cycles, memory);
                    let result = self.a as Word + value as Word + self.c as Word;

                    self.update_status_flags(UpdateStatusFlag::All as Byte, result, Some(value));
                    self.a = result as Byte;
                }
                INST_ADC_AY => {
                    let (_, value) = self.addr_absolute_y_read(&mut cycles, memory);
                    let result = self.a as Word + value as Word + self.c as Word;

                    self.update_status_flags(UpdateStatusFlag::All as Byte, result, Some(value));
                    self.a = result as Byte;
                }
                INST_ADC_IX => {
                    let (_, value) = self.addr_indirect_x_read(&mut cycles, memory);
                    let result = self.a as Word + value as Word + self.c as Word;

                    self.update_status_flags(UpdateStatusFlag::All as Byte, result, Some(value));
                    self.a = result as Byte;
                }
                INST_ADC_IY => {
                    let (_, value) = self.addr_indirect_y_read(&mut cycles, memory);
                    let result = self.a as Word + value as Word + self.c as Word;

                    self.update_status_flags(UpdateStatusFlag::All as Byte, result, Some(value));
                    self.a = result as Byte;
                }
                // AND Memory with Accumulator
                INST_AND_IM => {
                    let value = self.addr_immediate(&mut cycles, memory);
                    self.a &= value;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_AND_ZP => {
                    let (_, value) = self.addr_zero_page_read(&mut cycles, memory);
                    self.a &= value;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_AND_ZPX => {
                    let (_, value) = self.addr_zero_page_x_read(&mut cycles, memory);
                    self.a &= value;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_AND_A => {
                    let (_, value) = self.addr_absolute_read(&mut cycles, memory);
                    self.a &= value;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_AND_AX => {
                    let (_, value) = self.addr_absolute_x_read(&mut cycles, memory);
                    self.a &= value;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_AND_AY => {
                    let (_, value) = self.addr_absolute_y_read(&mut cycles, memory);
                    self.a &= value;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_AND_IX => {
                    let (_, value) = self.addr_indirect_x_read(&mut cycles, memory);
                    self.a &= value;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_AND_IY => {
                    let (_, value) = self.addr_indirect_y_read(&mut cycles, memory);
                    self.a &= value;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                // ASL Shift Left One Bit (Memory or Accumulator)
                INST_ASL_AC => {
                    let result: Word = (self.a as Word) << 1;
                    self.a = result as Byte;

                    cycles -= 1;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z | UpdateStatusFlag::C,
                        result,
                        None,
                    );
                }
                INST_ASL_ZP => {
                    let (addr, value) = self.addr_zero_page_read(&mut cycles, memory);
                    let result = (value as Word) << 1;

                    cycles -= 1;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z | UpdateStatusFlag::C,
                        result,
                        None,
                    );
                    self.write_byte(&mut cycles, memory, addr, result as Byte);
                }
                INST_ASL_ZPX => {
                    let (addr, value) = self.addr_zero_page_x_read(&mut cycles, memory);
                    let result = (value as Word) << 1;

                    cycles -= 1;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z | UpdateStatusFlag::C,
                        result,
                        None,
                    );
                    self.write_byte(&mut cycles, memory, addr, result as Byte);
                }
                INST_ASL_A => {
                    let (addr, value) = self.addr_absolute_read(&mut cycles, memory);
                    let result = (value as Word) << 1;

                    cycles -= 1;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z | UpdateStatusFlag::C,
                        result,
                        None,
                    );
                    self.write_byte(&mut cycles, memory, addr, result as Byte);
                }
                INST_ASL_AX => {
                    let (addr, value) = self.addr_absolute_x_read(&mut cycles, memory);
                    let result = (value as Word) << 1;

                    // Absolute X addressing mode takes 1 cycle more, and shift takes 1 cycle
                    cycles -= 2;

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z | UpdateStatusFlag::C,
                        result,
                        None,
                    );
                    self.write_byte(&mut cycles, memory, addr, result as Byte);
                }
                // BCC - Branch on Carry Clear
                INST_BCC => {
                    let offset = self.addr_immediate(&mut cycles, memory);
                    if self.c {
                        cycles -= 1;

                        let old_pc = self.pc;
                        self.pc = self.pc.wrapping_add(offset as Word);

                        // Check for page boundary crossed
                        if (old_pc & 0xFF00) != (self.pc & 0xFF00) {
                            cycles -= 1;
                        }
                    }
                }
                // LDA - Load Accumulator
                INST_LDA_IM => {
                    self.a = self.addr_immediate(&mut cycles, memory);

                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_LDA_ZP => {
                    let (_, value) = self.addr_zero_page_read(&mut cycles, memory);

                    self.a = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_LDA_ZPX => {
                    let (_, value) = self.addr_zero_page_x_read(&mut cycles, memory);

                    self.a = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_LDA_A => {
                    let (_, value) = self.addr_absolute_read(&mut cycles, memory);

                    self.a = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_LDA_AX => {
                    let (_, value) = self.addr_absolute_x_read(&mut cycles, memory);

                    self.a = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_LDA_AY => {
                    let (_, value) = self.addr_absolute_y_read(&mut cycles, memory);

                    self.a = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_LDA_IX => {
                    let (_, value) = self.addr_indirect_x_read(&mut cycles, memory);

                    self.a = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                INST_LDA_IY => {
                    let (_, value) = self.addr_indirect_y_read(&mut cycles, memory);

                    self.a = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.a as Word,
                        None,
                    );
                }
                // LDX - Load X Register
                INST_LDX_IM => {
                    self.x = self.addr_immediate(&mut cycles, memory);
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.x as Word,
                        None,
                    );
                }
                INST_LDX_ZP => {
                    let (_, value) = self.addr_zero_page_read(&mut cycles, memory);

                    self.x = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.x as Word,
                        None,
                    );
                }
                INST_LDX_ZPY => {
                    self.x = self.addr_zero_page_y_read(&mut cycles, memory);
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.x as Word,
                        None,
                    );
                }
                INST_LDX_A => {
                    let (_, value) = self.addr_absolute_read(&mut cycles, memory);

                    self.x = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.x as Word,
                        None,
                    );
                }
                INST_LDX_AY => {
                    let (_, value) = self.addr_absolute_y_read(&mut cycles, memory);

                    self.x = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.x as Word,
                        None,
                    );
                }
                // LDY - Load Y Register
                INST_LDY_IM => {
                    self.y = self.addr_immediate(&mut cycles, memory);
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.y as Word,
                        None,
                    );
                }
                INST_LDY_LZ => {
                    let (_, value) = self.addr_zero_page_read(&mut cycles, memory);

                    self.y = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.y as Word,
                        None,
                    );
                }
                INST_LDY_LZX => {
                    let (_, value) = self.addr_zero_page_x_read(&mut cycles, memory);

                    self.y = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.y as Word,
                        None,
                    );
                }
                INST_LDY_A => {
                    let (_, value) = self.addr_absolute_read(&mut cycles, memory);

                    self.y = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.y as Word,
                        None,
                    );
                }
                INST_LDY_AX => {
                    let (_, value) = self.addr_absolute_x_read(&mut cycles, memory);

                    self.y = value;
                    self.update_status_flags(
                        UpdateStatusFlag::N | UpdateStatusFlag::Z,
                        self.y as Word,
                        None,
                    );
                }
                // Store Accumulator in Memory
                INST_STA_ZP => {
                    self.addr_zero_page_write(&mut cycles, memory, self.a);
                }
                INST_STA_ZPX => {
                    self.addr_zero_page_x_write(&mut cycles, memory, self.a);
                }
                INST_STA_A => {
                    self.addr_absolute_write(&mut cycles, memory, self.a);
                }
                INST_STA_AX => {
                    self.addr_absolute_x_write(&mut cycles, memory, self.a);
                }
                INST_STA_AY => {
                    self.addr_absolute_y_write(&mut cycles, memory, self.a);
                }
                INST_STA_IX => {
                    self.addr_indirect_x_write(&mut cycles, memory, self.a);
                }
                INST_STA_IY => {
                    self.addr_indirect_y_write(&mut cycles, memory, self.a);
                }
                _ => {
                    unreachable!()
                }
            };
        }

        cycles
    }

    fn update_status_flags(&mut self, flags: Byte, result: Word, value: Option<Byte>) {
        // Negative Flag: Set if bit 7 of the result is set
        if flags & UpdateStatusFlag::N as Byte != 0 {
            self.n = (result & 0x80) != 0;
        }

        if flags & UpdateStatusFlag::Z as Byte != 0 {
            self.z = (result & 0xFF) == 0;
        }

        // Carry Flag: Set if the 16-but result is greater then 255
        if flags & UpdateStatusFlag::C as Byte != 0 {
            self.c = result > 0xFF;
        }

        // Overflow Flag: Set if the sign of the result is different from the sign of the accumulator
        // and the sign of the operand
        if flags & UpdateStatusFlag::V as Byte != 0 {
            let value = value.expect("Value is required for V flag");
            let result = result as Byte;
            self.v = (self.a ^ result) & (value ^ result) & 0x80 != 0;
        }
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

    /// Dump memory content from specified address range, or whole memory if
    /// address is not provided
    pub fn dump(&self, addr: Option<(Word, Word)>) {
        let (start, end) = match addr {
            Some((start, end)) => (start as usize, end as usize),
            None => (0, MAX_MEM),
        };

        for i in start..=end {
            println!("0x{:0>4X}: 0x{:0>2X}", i, self.0[i]);
        }
    }
}

#[cfg(test)]
mod tests {
    const OPCODE_ADDR: Word = ENTRY_POINT;
    const OPERAND_1_ADDR: Word = ENTRY_POINT + 1;
    const OPERAND_2_ADDR: Word = OPERAND_1_ADDR + 1;

    use std::mem;

    use super::*;

    fn init() -> (Cpu, Mem) {
        let mut memory = Mem::new();
        let mut cpu = Cpu::new();
        cpu.reset(&mut memory);

        (cpu, memory)
    }

    #[test]
    fn status_flags_nzc() {
        let (mut cpu, mut memory) = init();

        cpu.update_status_flags(
            UpdateStatusFlag::N | UpdateStatusFlag::Z | UpdateStatusFlag::C,
            0xFFFF,
            None,
        );

        assert!(cpu.n);
        assert!(!cpu.z);
        assert!(cpu.c);

        cpu.reset(&mut memory);

        cpu.update_status_flags(
            UpdateStatusFlag::N | UpdateStatusFlag::Z | UpdateStatusFlag::C,
            0x0000,
            None,
        );

        assert!(!cpu.n);
        assert!(cpu.z);
        assert!(!cpu.c);
    }

    #[test]
    fn status_flag_v() {
        let (mut cpu, mut memory) = init();

        // 0x40 + 0x40 = 0x80 - overflow
        cpu.a = 0x40;
        cpu.update_status_flags(UpdateStatusFlag::V as Byte, 0xFF, Some(0x40));

        assert!(cpu.v);

        cpu.reset(&mut memory);

        // 0xF0 + 0x0F = 0xFF - no overflow (because 7-th bit of A is 1)
        cpu.a = 0xF0;
        cpu.update_status_flags(UpdateStatusFlag::V as Byte, 0xFF, Some(0xF0));

        assert!(!cpu.v);
    }

    #[test]
    fn inst_and_im() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_AND_IM);
        memory.write_byte(OPERAND_1_ADDR, 0b1010_1010);
        cpu.a = 0b1100_1100;

        cpu.exec(2, &mut memory);

        assert_eq!(cpu.a, 0b1000_1000);
        assert!(cpu.n);
        assert!(!cpu.z);
    }

    #[test]
    fn inst_and_zp() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_AND_ZP);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x01, 0b1010_1010);
        cpu.a = 0b1100_1100;

        cpu.exec(3, &mut memory);

        assert_eq!(cpu.a, 0b1000_1000);
        assert!(cpu.n);
        assert!(!cpu.z);
    }

    #[test]
    fn inst_and_zpx() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_AND_ZPX);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x02, 0b1010_1010);
        cpu.x = 0x01;
        cpu.a = 0b1100_1100;

        cpu.exec(4, &mut memory);
        assert_eq!(cpu.a, 0b1000_1000);
        assert!(cpu.n);
        assert!(!cpu.z);
    }

    #[test]
    fn inst_and_a() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_AND_A);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1234, 0b1010_1010);
        cpu.a = 0b1100_1100;

        cpu.exec(4, &mut memory);
        assert_eq!(cpu.a, 0b1000_1000);
        assert!(cpu.n);
        assert!(!cpu.z);
    }

    #[test]
    fn inst_and_ax() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_AND_AX);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1235, 0b1010_1010);

        cpu.x = 0x01;
        cpu.a = 0b1100_1100;

        cpu.exec(4, &mut memory);
        assert_eq!(cpu.a, 0b1000_1000);
        assert!(cpu.n);
        assert!(!cpu.z);
    }

    #[test]
    fn inst_and_ay() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_AND_AY);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1235, 0b1010_1010);

        cpu.y = 0x01;
        cpu.a = 0b1100_1100;

        cpu.exec(4, &mut memory);
        assert_eq!(cpu.a, 0b1000_1000);
        assert!(cpu.n);
        assert!(!cpu.z);
    }

    #[test]
    fn inst_and_ix() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_AND_IX);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x0002, 0x12);
        memory.write_byte(0x0003, 0x34);
        memory.write_byte(0x1234, 0b1010_1010);

        cpu.x = 0x01;
        cpu.a = 0b1100_1100;

        cpu.exec(6, &mut memory);
        assert_eq!(cpu.a, 0b1000_1000);
        assert!(cpu.n);
        assert!(!cpu.z);
    }

    #[test]
    fn inst_and_iy() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_AND_IY);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x0001, 0x12);
        memory.write_byte(0x0002, 0x34);
        memory.write_byte(0x1235, 0b1010_1010);

        cpu.y = 0x01;
        cpu.a = 0b1100_1100;

        cpu.exec(5, &mut memory);
        assert_eq!(cpu.a, 0b1000_1000);
        assert!(cpu.n);
        assert!(!cpu.z);
    }

    #[test]
    fn inst_adc_im() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_ADC_IM);
        memory.write_byte(OPERAND_1_ADDR, 0xF0);

        cpu.a = 0x0E;
        cpu.c = true;
        cpu.exec(2, &mut memory);

        // 0xF0 + 0x0E + 1 (carry) = 0xFF
        assert_eq!(cpu.a, 0xFF);
        assert!(!cpu.c);
        assert!(!cpu.z);
        assert!(!cpu.v);
        assert!(cpu.n);
    }

    #[test]
    fn inst_adc_zp() {
        let (mut cpu, mut memory) = init();
        memory.write_byte(OPCODE_ADDR, INST_ADC_ZP);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x0001, 0xF0);

        cpu.a = 0x0E;
        cpu.c = true;
        cpu.exec(3, &mut memory);

        // 0xF0 + 0x0E + 1 (carry) = 0xFF
        assert_eq!(cpu.a, 0xFF);
        assert!(!cpu.c);
        assert!(!cpu.z);
        assert!(!cpu.v);
        assert!(cpu.n);
    }

    #[test]
    fn inst_adc_zpx() {
        let (mut cpu, mut memory) = init();
        memory.write_byte(OPCODE_ADDR, INST_ADC_ZPX);

        // Zero Page + X Offset: 0x01 + 0x01 = 0x02
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        cpu.x = 0x01;

        memory.write_byte(0x02, 0xF0);
        cpu.a = 0x0E;
        cpu.c = true;

        cpu.exec(4, &mut memory);

        // 0xF0 + 0x0E + 1 (carry) = 0xFF
        assert_eq!(cpu.a, 0xFF);
        assert!(!cpu.c);
        assert!(!cpu.z);
        assert!(!cpu.v);
        assert!(cpu.n);
    }

    #[test]
    fn inst_adc_a() {
        let (mut cpu, mut memory) = init();
        memory.write_byte(OPCODE_ADDR, INST_ADC_A);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);

        memory.write_byte(0x1234, 0xF0);
        cpu.a = 0x0E;
        cpu.c = true;
        cpu.exec(4, &mut memory);

        // 0xF0 + 0x0E + 1 (carry) = 0xFF
        assert_eq!(cpu.a, 0xFF);
        assert!(!cpu.c);
        assert!(!cpu.z);
        assert!(!cpu.v);
        assert!(cpu.n);
    }

    #[test]
    fn inst_adc_ax() {
        let (mut cpu, mut memory) = init();
        memory.write_byte(OPCODE_ADDR, INST_ADC_AX);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        cpu.x = 0x01;

        memory.write_byte(0x1235, 0xF0);
        cpu.a = 0x0E;
        cpu.c = true;
        cpu.exec(4, &mut memory);

        // 0xF0 + 0x0E + 1 (carry) = 0xFF
        assert_eq!(cpu.a, 0xFF);
        assert!(!cpu.c);
        assert!(!cpu.z);
        assert!(!cpu.v);
        assert!(cpu.n);
    }

    #[test]
    fn inst_adc_ay() {
        let (mut cpu, mut memory) = init();
        memory.write_byte(OPCODE_ADDR, INST_ADC_AY);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        cpu.y = 0x01;

        memory.write_byte(0x1235, 0xF0);
        cpu.a = 0x0E;
        cpu.c = true;
        cpu.exec(4, &mut memory);

        // 0xF0 + 0x0E + 1 (carry) = 0xFF
        assert_eq!(cpu.a, 0xFF);
        assert!(!cpu.c);
        assert!(!cpu.z);
        assert!(!cpu.v);
        assert!(cpu.n);
    }

    #[test]
    fn inst_adc_ix() {
        let (mut cpu, mut memory) = init();
        memory.write_byte(OPCODE_ADDR, INST_ADC_IX);

        // Indirect Addressing: 0x01 + 0x01 = 0x02
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        cpu.x = 0x01;

        // Value address: 0x0400
        memory.write_byte(0x0002, 0x04);

        // 0xF0 + 0x0E + 1 (carry) = 0xFF
        memory.write_byte(0x0400, 0xF0);
        cpu.a = 0x0E;
        cpu.c = true;

        cpu.exec(6, &mut memory);

        // 0xF0 + 0x0E + 1 (carry) = 0xFF
        assert_eq!(cpu.a, 0xFF);
        assert!(!cpu.c);
        assert!(!cpu.z);
        assert!(!cpu.v);
        assert!(cpu.n);
    }

    #[test]
    fn inst_adc_iy() {
        let (mut cpu, mut memory) = init();
        memory.write_byte(OPCODE_ADDR, INST_ADC_IY);

        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x0001, 0x03);
        memory.write_byte(0x0002, 0x00);
        cpu.y = 0x01;

        // 0xF0 + 0x0E + 1 (carry) = 0xFF
        memory.write_byte(0x0301, 0xF0);
        cpu.a = 0x0E;
        cpu.c = true;

        cpu.exec(5, &mut memory);

        // 0xF0 + 0x0E + 1 (carry) = 0xFF
        assert_eq!(cpu.a, 0xFF);
        assert!(!cpu.c);
        assert!(!cpu.z);
        assert!(!cpu.v);
        assert!(cpu.n);
    }

    #[test]
    fn inst_asl_ac() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_ASL_AC);
        cpu.a = 0x7F;
        cpu.exec(2, &mut memory);

        assert_eq!(cpu.a, 0xFE);
        assert!(cpu.n);
        assert!(!cpu.z);
        assert!(!cpu.c);
    }

    #[test]
    fn inst_asl_zp() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_ASL_ZP);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x0001, 0x7F);
        cpu.exec(5, &mut memory);

        assert_eq!(memory.read_byte(0x0001), 0xFE);
        assert!(cpu.n);
        assert!(!cpu.z);
        assert!(!cpu.c);
    }

    #[test]
    fn inst_asl_zpx() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_ASL_ZPX);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x02, 0x7F);
        cpu.x = 0x01;

        cpu.exec(6, &mut memory);

        assert_eq!(memory.read_byte(0x02), 0xFE);
        assert!(cpu.n);
        assert!(!cpu.z);
        assert!(!cpu.c);
    }

    #[test]
    fn inst_asl_a() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_ASL_A);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1234, 0x7F);

        cpu.exec(6, &mut memory);

        assert_eq!(memory.read_byte(0x1234), 0xFE);
        assert!(cpu.n);
        assert!(!cpu.z);
        assert!(!cpu.c);
    }

    #[test]
    fn inst_asl_ax() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_ASL_AX);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1235, 0x7F);
        cpu.x = 0x01;

        cpu.exec(7, &mut memory);

        assert_eq!(memory.read_byte(0x1235), 0xFE);
        assert!(cpu.n);
        assert!(!cpu.z);
        assert!(!cpu.c);
    }

    #[test]
    fn inst_bcc() {
        let (mut cpu, mut memory) = init();

        // Test branch taken
        memory.write_byte(OPCODE_ADDR, INST_BCC);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        cpu.c = true;

        cpu.exec(3, &mut memory);

        assert_eq!(cpu.pc, ENTRY_POINT + 0x03); // 0x2 is the size of the instruction + 0x01 offset

        // Reset CPU
        cpu.reset(&mut memory);

        // Test branch not taken
        memory.write_byte(OPCODE_ADDR, INST_BCC);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        cpu.c = false;

        cpu.exec(2, &mut memory);

        assert_eq!(cpu.pc, ENTRY_POINT + 0x02);

        // Test page boundary crossed
        memory.write_byte(OPCODE_ADDR, INST_BCC);
        memory.write_byte(OPERAND_1_ADDR, 0xFF);
        cpu.c = true;

        cpu.exec(4, &mut memory);

        assert_eq!(cpu.pc, ENTRY_POINT + 0x2 + 0xFF); // 0x2 is the size of the instruction
    }

    #[test]
    fn inst_lda_im() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDA_IM);
        memory.write_byte(OPERAND_1_ADDR, 0x0F);

        let cycles = cpu.exec(2, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_lda_zp() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDA_ZP);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x0001, 0x0F);

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_lda_zpx() {
        let (mut cpu, mut memory) = init();

        // Take with no overflow
        memory.write_byte(OPCODE_ADDR, INST_LDA_ZPX);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x02, 0x0F);
        cpu.x = 0x01;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);

        // Reset CPU
        cpu.reset(&mut memory);

        // Take with overflow
        memory.write_byte(OPCODE_ADDR, INST_LDA_ZPX);
        memory.write_byte(OPERAND_1_ADDR, 0xFF);
        memory.write_byte(0x7F, 0x0F);
        cpu.x = 0x80;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_lda_a() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDA_A);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1234, 0x0F);

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_lda_ax() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDA_AX);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1235, 0x0F);
        cpu.x = 0x01;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_lda_ay() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDA_AY);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1235, 0x0F);
        cpu.y = 0x01;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_lda_ix() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDA_IX);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        cpu.x = 0x33;

        memory.write_byte(0x0045, 0x01);
        memory.write_byte(0x0046, 0x02);
        memory.write_byte(0x0102, 0x0F);

        let cycles = cpu.exec(6, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_lda_iy() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDA_IY);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x0001, 0x01);
        memory.write_byte(0x0002, 0x02);
        cpu.y = 0x03;

        memory.write_byte(0x0105, 0x0F);

        let cycles = cpu.exec(5, &mut memory);

        assert_eq!(cpu.a, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_ldx_im() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDX_IM);
        memory.write_byte(OPERAND_1_ADDR, 0x0F);
        let cycles = cpu.exec(2, &mut memory);

        assert_eq!(cpu.x, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_ldx_zp() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDX_ZP);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x0001, 0x0F);

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(cpu.x, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_ldx_zpy() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDX_ZPY);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x02, 0x0F);
        cpu.y = 0x01;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.x, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_ldx_a() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDX_A);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1234, 0x0F);

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.x, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_ldx_ay() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDX_AY);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1235, 0x0F);
        cpu.y = 0x01;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.x, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_ldy_im() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDY_IM);
        memory.write_byte(OPERAND_1_ADDR, 0x0F);
        let cycles = cpu.exec(2, &mut memory);

        assert_eq!(cpu.y, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_ldy_lz() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDY_LZ);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x0001, 0x0F);

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(cpu.y, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_ldy_lzx() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDY_LZX);
        memory.write_byte(OPERAND_1_ADDR, 0x01);
        memory.write_byte(0x02, 0x0F);
        cpu.x = 0x01;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.y, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_ldy_a() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDY_A);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1234, 0x0F);

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.y, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_ldy_ax() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_LDY_AX);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        memory.write_byte(0x1235, 0x0F);
        cpu.x = 0x01;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cpu.y, 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_sta_zp() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_STA_ZP);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        cpu.a = 0x0E;

        let cycles = cpu.exec(3, &mut memory);

        assert_eq!(memory.read_byte(0x0012), 0x0E);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_sta_zpx() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_STA_ZPX);
        memory.write_byte(OPERAND_1_ADDR, 0x0E);
        cpu.x = 0x01;
        cpu.a = 0x0E;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cycles, 0);
        assert_eq!(memory.read_byte(0x000F), 0x0E);
    }

    #[test]
    fn inst_sta_a() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_STA_A);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        cpu.a = 0xE;

        let cycles = cpu.exec(4, &mut memory);

        assert_eq!(cycles, 0);
        assert_eq!(memory.read_byte(0x1234), 0xE);
    }

    #[test]
    fn inst_sta_ax() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_STA_AX);

        // Mem address: 0x1235
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        cpu.a = 0x0F;
        cpu.x = 0x01;

        let cycles = cpu.exec(4, &mut memory);
        assert_eq!(cycles, 0);
        assert_eq!(memory.read_byte(0x1235), 0x0F);
    }

    #[test]
    fn inst_sta_ay() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_STA_AY);

        // Mem address: 0x1235
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        cpu.a = 0x0F;
        cpu.y = 0x01;

        let cycles = cpu.exec(4, &mut memory);
        assert_eq!(cycles, 0);
        assert_eq!(memory.read_byte(0x1235), 0x0F);
    }

    #[test]
    fn inst_sta_ix() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_STA_IX);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        cpu.x = 0x33;

        memory.write_byte(0x0045, 0x01);
        memory.write_byte(0x0046, 0x02);
        cpu.a = 0x0F;

        let cycles = cpu.exec(6, &mut memory);

        assert_eq!(memory.read_byte(0x0102), 0x0F);
        assert_eq!(cycles, 0);
    }

    #[test]
    fn inst_sta_iy() {
        let (mut cpu, mut memory) = init();

        memory.write_byte(OPCODE_ADDR, INST_STA_IY);
        memory.write_byte(OPERAND_1_ADDR, 0x12);
        memory.write_byte(OPERAND_2_ADDR, 0x34);
        cpu.y = 0x01;

        memory.write_byte(0x1235, 0x0F);
        cpu.a = 0x0F;

        let cycles = cpu.exec(5, &mut memory);

        assert_eq!(memory.read_byte(0x1235), 0x0F);
        assert_eq!(cycles, 0);
    }
}
