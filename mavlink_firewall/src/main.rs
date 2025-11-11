use mavlink_parser_vest::{
    MavCmd, MavlinkMsg, MavlinkMsgMsg, MavlinkV1MsgPayload, MavlinkV2MsgPayload, parse_mavlink_msg,
};
use mavlink_parser_vest::{
    SpecMavlinkMsg, SpecMavlinkMsgMsg, SpecMavlinkV1MsgPayload, SpecMavlinkV2MsgPayload,
    spec_mavlink_msg,
};
use vest::properties::SpecCombinator;
use vstd::prelude::*;

verus! {

pub open spec fn spec_firewall(packet: Seq<u8>) -> bool
{
    match spec_mavlink_msg().spec_parse(packet) {
        Some((_, msg)) => spec_can_send(msg),
        None => false,
    }
}

pub open spec fn spec_can_send(msg: SpecMavlinkMsg) -> bool
{
    !spec_msg_is_flash_bootloader(msg)
}

pub open spec fn spec_msg_is_flash_bootloader(msg: SpecMavlinkMsg) -> bool
{
    spec_msg_v1_is_flash_bootloader(msg) || spec_msg_v2_is_flash_bootloader(msg)
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
    ensures
        r == spec_firewall(packet@)
{
    match parse_mavlink_msg(packet) {
        Ok((_, msg)) => can_send(&msg),
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
            MavlinkV1MsgPayload::CommandInt(cmd_int) => {
                Some(cmd_int.command)
            }
            MavlinkV1MsgPayload::CommandLong(cmd_long) => {
                Some(cmd_long.command)
            }
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

    let can_send = firewall(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}");

    let packet = [
        0xfdu8, 0x12, // |.......+|
        // 0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
        0x00, 0x00, 0x71, 0xff, 0xbe, 0x86, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x8f, 0x19, 0x7c, 0x40, 0xf6, 0xcc, // |1...|@..|
        0x31, 0x92, 0x8f, 0x19, 0x7c, 0x40, 0xf6, 0xcc, // |1...|@..|
        0x64, 0x00, 0x2c, 0xc7,
    ];

    let can_send = firewall(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}");

    let packet = [
        0xfdu8, 0x21, // |.......+|
        0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x9A, 0xA6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x2c, 0xc7,
    ];

    let can_send = firewall(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}");

    let packet = [
        0xfdu8, 0x21, // |.......+|
        0x00, 0x00, 0x71, 0xff, 0xbe, 0x8c, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x9A, 0xA6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x2c, 0xc7,
    ];

    let can_send = firewall(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}");

    let packet = [
        0xfdu8, 0x0a, // |.......+|
        0x00, 0x00, 0x71, 0xff, 0xbe, 77, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x00, 0x64, 0x00, 0x00, 0x00, 0x00, 0x20, 0x30, 0x2c, 0xc7,
    ];

    let can_send = firewall(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}");

    let packet = [
        0xfdu8, 0x21, // |.......+|
        0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x53, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x2c, 0xc7,
    ];

    let can_send = firewall(&packet);
    println!("packet {packet:?}\ncan_send: {can_send}");
}
