use mavlink_parser_vest::{
    CommandAck, CommandInt, MavlinkMsg, MavlinkMsgCombinator, MavlinkMsgMsg,
    MavlinkV1MsgCombinatorAlias, MavlinkV1MsgPayload, MavlinkV2MsgPayload, SpecMavlinkMsg,
    SpecMavlinkMsgCombinator, mavlink_msg, parse_mavlink_msg, spec_mavlink_msg,
    spec_mavlink_msg_msg,
};
use vest::buf_traits::From;
use vest::errors::ParseError;
use vest::properties::SecureSpecCombinator;
use vest::properties::{Combinator, SpecCombinator};
use vest::utils::SpecInto;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

fn firewall(packet: &[u8]) -> (r: bool)
    ensures
        match spec_mavlink_msg().spec_parse(packet@) {
            Some((size, val)) => r == !spec_msg_is_flash_bootloader(val),
            None => r == false,
        }
{
        match parse_mavlink_msg(packet) {
            Ok((_curr_len, msg)) => {
                can_send(&msg)
            }
            Err(e) => {
                false
            }
        }

}


pub open spec fn spec_msg_is_flash_bootloader(msg: SpecMavlinkMsg) -> bool
{
    (msg.msg is MavLink1 &&
        msg.msg->MavLink1_0.payload is CommandInt &&
        msg.msg->MavLink1_0.payload->CommandInt_0.command == mavlink_parser_vest::MavCmd::SPEC_FlashBootloader) ||
    (msg.msg is MavLink1 &&
        msg.msg->MavLink1_0.payload is CommandLong &&
        msg.msg->MavLink1_0.payload->CommandLong_0.command == mavlink_parser_vest::MavCmd::SPEC_FlashBootloader) ||
    (msg.msg is MavLink2 &&
        msg.msg->MavLink2_0.payload is CommandInt &&
        msg.msg->MavLink2_0.payload->CommandInt_0.command == mavlink_parser_vest::MavCmd::SPEC_FlashBootloader) ||
    (msg.msg is MavLink2 &&
        msg.msg->MavLink2_0.payload is CommandLong &&
        msg.msg->MavLink2_0.payload->CommandLong_0.command == mavlink_parser_vest::MavCmd::SPEC_FlashBootloader)

}

fn can_send(msg: &MavlinkMsg) -> (r: bool)
    ensures
        spec_msg_is_flash_bootloader(msg@) == (r == false)
{
    match &msg.msg {
        MavlinkMsgMsg::MavLink1(v1_msg) => match &v1_msg.payload {
            MavlinkV1MsgPayload::CommandInt(cmd_int) => {
                cmd_int.command != mavlink_parser_vest::MavCmd::FlashBootloader
            }
            MavlinkV1MsgPayload::CommandLong(cmd_long) => {
                cmd_long.command != mavlink_parser_vest::MavCmd::FlashBootloader
            }
            _ => true,
        },
        MavlinkMsgMsg::MavLink2(v2_msg) => match &v2_msg.payload {
            MavlinkV2MsgPayload::CommandInt(cmd_int) => {
                cmd_int.command != mavlink_parser_vest::MavCmd::FlashBootloader
            }
            MavlinkV2MsgPayload::CommandLong(cmd_long) => {
                cmd_long.command != mavlink_parser_vest::MavCmd::FlashBootloader
            }
            _ => true,
        },
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
