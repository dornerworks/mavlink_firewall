use mavlink_parser_vest::spec_mavlink_msg_msg;
use mavlink_parser_vest::{
    MavCmd, MavlinkMsg, MavlinkMsgMsg, MavlinkV1MsgPayload, MavlinkV2MsgPayload, parse_mavlink_msg,
};
use mavlink_parser_vest::{
    SpecMavlinkMsg, SpecMavlinkMsgMsg, SpecMavlinkV1MsgPayload, SpecMavlinkV2MsgPayload,
    spec_mavlink_msg,
};
use vest::properties::SecureSpecCombinator;
use vest::properties::SpecCombinator;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

pub open spec fn spec_firewall(packet: Seq<u8>) -> bool
{
    match spec_mavlink_msg().spec_parse(packet) {
        Some((_, msg)) => {
            spec_can_send(msg)
        },
        None => false,
    }
}

pub open spec fn spec_can_send(msg: SpecMavlinkMsg) -> bool
{
    !spec_msg_is_flash_bootloader(msg)
}

pub open spec fn spec_msg_is_flash_bootloader(msg: SpecMavlinkMsg) -> bool
{
    // spec_msg_v1_is_flash_bootloader(msg) ||
    spec_msg_v2_is_flash_bootloader(msg)
}

pub open spec fn spec_msg_v1_is_flash_bootloader(msg: SpecMavlinkMsg) -> bool
{
    msg.msg matches SpecMavlinkMsgMsg::MavLink1(mv1) &&
        match mv1.payload {
            SpecMavlinkV1MsgPayload::CommandInt(pay) => pay.command == MavCmd::SPEC_FlashBootloader,
            SpecMavlinkV1MsgPayload::CommandLong(pay) => pay.command == MavCmd::SPEC_FlashBootloader,
            _ => false
        }
}

pub open spec fn spec_msg_v2_is_flash_bootloader(msg: SpecMavlinkMsg) -> bool
{
    msg.msg matches SpecMavlinkMsgMsg::MavLink2(mv2) &&
        match mv2.payload {
            SpecMavlinkV2MsgPayload::CommandInt(pay) => pay.command == MavCmd::SPEC_FlashBootloader,
            SpecMavlinkV2MsgPayload::CommandLong(pay) => pay.command == MavCmd::SPEC_FlashBootloader,
            _ => false
        }
}

fn firewall(packet: &[u8]) -> (r: bool)
    // requires
    //         packet@.len() <= usize::MAX,
    // requires
    //     spec_mavlink_msg().requires(),
    ensures
        r == spec_firewall(packet@),
        spec_mavlink_msg().spec_parse(packet@).is_some() && spec_msg_is_flash_bootloader(spec_mavlink_msg().spec_parse(packet@).unwrap().1) ==> spec_gumbo_msg_is_mav_cmd_flash_bootloader(packet@),
{
    match parse_mavlink_msg(packet) {
        Ok((len, msg)) => {
            assume(spec_mavlink_msg().requires());
            proof {
                spec_mavlink_msg().theorem_parse_serialize_roundtrip(packet@);
                spec_mavlink_msg().lemma_parse_length(packet@);
            }
            let ghost s = spec_mavlink_msg().spec_serialize(msg@);

            assert(s.len() == len);

            let ghost in_buf = packet@.take(len as int);
            let ghost out_buf = s.take(len as int);

            // We can relate an input buf to a roundtrip parsed-serialized buf
            assert(in_buf == out_buf);
            assert(in_buf =~= out_buf);
            assert(mavlink_is_v2(in_buf) == mavlink_is_v2(out_buf));

            // However, I am not sure how I can relate either bufs to the parsed object
            assert(msg@.msg is MavLink2 ==> mavlink_is_v2(out_buf));

            // assert(spec_gumbo_msg_is_mav_cmd_flash_bootloader(packet@) ==> spec_msg_is_flash_bootloader(msg@));
            // assert(spec_msg_is_flash_bootloader(msg@) ==> spec_gumbo_msg_is_mav_cmd_flash_bootloader(s));

            can_send(&msg)
        }
        Err(_) => false,
    }
}

fn can_send(msg: &MavlinkMsg) -> (r: bool)
    ensures
        r == spec_can_send(msg@),
{
    !msg_is_flash_bootloader(msg)
}

fn msg_is_flash_bootloader(msg: &MavlinkMsg) -> (r: bool)
    ensures
         r == spec_msg_is_flash_bootloader(msg@)
{
    let command = match &msg.msg {
        MavlinkMsgMsg::MavLink1(v1_msg) => match &v1_msg.payload {
            // MavlinkV1MsgPayload::CommandInt(cmd_int) => {
            //     Some(cmd_int.command)
            // }
            // MavlinkV1MsgPayload::CommandLong(cmd_long) => {
            //     Some(cmd_long.command)
            // }
            _ => None,
        },
        MavlinkMsgMsg::MavLink2(v2_msg) => match &v2_msg.payload {
            MavlinkV2MsgPayload::CommandInt(cmd_int) => {
                Some(cmd_int.command)
            }
            MavlinkV2MsgPayload::CommandLong(cmd_long) => {
                Some(cmd_long.command)
            }
            _ => None,
        },

    };

    match command {
        Some(cmd) => cmd == MavCmd::FlashBootloader,
        None => false,
    }

}

pub open spec fn two_bytes_to_u16(
  byte0: u8,
  byte1: u8) -> u16
{
  (((byte1) as u16) * 256u16 + ((byte0) as u16)) as u16
}


pub open spec fn three_bytes_to_u32(
  byte0: u8,
  byte1: u8,
  byte2: u8,
) -> u32
{
  ((((byte2) as u32) * 65536u32 + ((byte1) as u32) * 256u32 + ((byte0) as u32))) as u32
}

pub open spec fn msg_is_command_int(msg: Seq<u8>) -> bool {
    // msg.subrange(7, 10) =~= seq![75,0,0]
    three_bytes_to_u32(msg[7], msg[8], msg[9]) == 75u32

    // msg.subrange(7, 10) =~= seq![0,0,75]
}

pub open spec fn command_int_msg_is_bootloader_flash(msg: Seq<u8>) -> bool {
    // two_bytes_to_u16(msg[13], msg[12]) == 42650u16
    two_bytes_to_u16(msg[13], msg[14]) == 42650u16
}

pub open spec fn msg_is_command_long(msg: Seq<u8>) -> bool {
    // msg.subrange(7, 10) =~= seq![76,0,0]
    three_bytes_to_u32(msg[7], msg[8], msg[9]) == 76u32
    // msg.subrange(7, 10) =~= seq![0,0,76]
}

pub open spec fn command_long_msg_is_bootloader_flash(msg: Seq<u8>) -> bool {
    // two_bytes_to_u16(msg[14], msg[13]) == 42650u16
    two_bytes_to_u16(msg[12], msg[13]) == 42650u16
}

pub open spec fn mavlink_is_v2(msg: Seq<u8>) -> bool
{
    msg[0] == 0xFDu8
}

pub open spec fn spec_gumbo_msg_is_mav_cmd_flash_bootloader(msg: Seq<u8>) -> bool
{
mavlink_is_v2(msg) && ((msg_is_command_int(msg) && command_int_msg_is_bootloader_flash(msg)) ||
    (msg_is_command_long(msg) && command_long_msg_is_bootloader_flash(msg)))
}


pub fn time_triggered(packet: &[u8]) -> (r: bool)
    requires
        packet.len() > 20,
    ensures
        spec_gumbo_msg_is_mav_cmd_flash_bootloader(packet@) ==> (r == false),
{

    // let msg_id = ((((packet[9]) as u32) * 65536u32 + ((packet[8]) as u32) * 256u32 + ((packet[7]) as u32))) as u32;
    // let mav_cmd = (( ((packet[13]) as u16) * 256u16 + ((packet[12]) as u16))) as u16;
    // print_msg_id(msg_id);
    // print_mav_cmd(mav_cmd);
    firewall(packet)
}


    // let mut i = 0;
    // while i < msg.len()
    //  invariant
    //     0 <= i <= msg@.len(),
    //     forall |j| 0 <= j < i ==> packet@[j] == msg@[j],
    // decreases
    //     msg@.len() - i
    // {
    //     packet[i] = msg[i];
    //     i += 1;
    // }

    #[verifier::external_body]
    fn print_msg_id(val: u32) {
        println!("msg_id: {val}");
    }

    #[verifier::external_body]
    fn print_mav_cmd(val: u16) {
        println!("mav_cmd: {val}");
    }
}

fn main() {
    let packet = [
        0xfdu8, 0x13, // |.......+|
        // 0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
        0x00, 0x00, 0x71, 0xff, 0xbe, 0x86, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x8f, 0x19, 0x7c, 0x40, 0xf6, 0xcc, // |1...|@..|
        0x31, 0x92, 0x8f, 0x19, 0x7c, 0x40, 0xf6, 0xcc, // |1...|@..|
        0x64, 0x00, 0x2c, 0xc7,
    ];

    let can_send = time_triggered(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}\n");

    let packet = [
        0xfdu8, 0x12, // |.......+|
        // 0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
        0x00, 0x00, 0x71, 0xff, 0xbe, 0x86, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x8f, 0x19, 0x7c, 0x40, 0xf6, 0xcc, // |1...|@..|
        0x31, 0x92, 0x8f, 0x19, 0x7c, 0x40, 0xf6, 0xcc, // |1...|@..|
        0x64, 0x00, 0x2c, 0xc7,
    ];

    let can_send = time_triggered(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}\n");

    let packet = [
        0xfdu8, 0x21, // |.......+|
        0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x9A, 0xA6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x2c, 0xc7,
    ];

    let can_send = time_triggered(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}\n");

    let packet = [
        0xfdu8, 0x21, // |.......+|
        0x00, 0x00, 0x71, 0xff, 0xbe, 0x8c, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x9A, 0xA6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x2c, 0xc7,
    ];

    let can_send = time_triggered(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}\n");

    let packet = [
        0xfdu8, 0x0a, // |.......+|
        0x00, 0x00, 0x71, 0xff, 0xbe, 77, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x00, 0x64, 0x00, 0x00, 0x00, 0x00, 0x20, 0x30, 0x2c, 0xc7,
    ];

    let can_send = time_triggered(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}\n");

    let packet = [
        0xfdu8, 0x21, // |.......+|
        0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x53, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x2c, 0xc7,
    ];

    let can_send = time_triggered(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}\n");
}
