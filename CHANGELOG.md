# Changelog

## [0.0.3] - 2022-05-31

### Fixed

- Fix documentation for peer module types

### Changed

- Add `InfoHash` fmt implementations

- Add `Id` and `ReservedBytes` fmt implementations

- Add `const`, `#[must]`, and `#[inline]` to various types

- Add `pub` to stable newtypes

### Added

- Add DHT Node `Id` and `CompactAddress` types

- Add KRPC traits and common message types for error, ping, find_node,
  announce_peer and get_peers

- Add KRPC transaction `Id` and collection types

- Add DHT Routing types to manage known nodes

## [0.0.2] - 2022-04-27

### Fixed

- Fix IndexBitfield::from_slice()

  from_slice() took a raw byte slice which did not give enough
  information about the length of the bitfield. Unused bytes would
  increase the size.

### Changed

- Remove clones for is_superset and is_subset

  Remove the need to take ownership which usually resulted in a clone of
  the IndexBitfield for is_superset() and is_subset().

- Simplify IndexBitfield API

  Add simple getter/setter for IndexBitfield to get/set bool for index

- Add type parameter for IndexCountedSet

  In most cases, `u8` should be enough but in case a larger number of
  peers are simultaneously connected.

### Added

- Add time::Instant trait

  Add `Instant` trait for portability

- Add peer::MetricsHistory

  `MetricsHistory` can be used to store regular intervals of history.
  Useful to make decisions based on metric averages over a period of
  time.

- Add peer::Session for managing peer state

  `Session` maintains the various state changes for peers when a message
  is received or sent.

  Make `peer::State` and `peer::SendState` private to allow
  implementation details to change.

- Add max_index() to IndexBitfield and IndexCountedSet

- Add peer::Metrics and peer::State

  Metrics contain both the current interval's metrics and a running
  total of accumulated metrics.

  peer::State contains the local and remote state as well as deadlines
  for read and write.

- Add protocol::Metrics methods for specific types

  Allow individual message type metrics to be added to skip the match
  expression if the message type is already known

- Adds IndexBitfield::clear_with_max_index

  Enables reuse of the IndexBitfield by clearing and resizing to the new
  maximum piece index.

- Add generational index and vector types

  Generational vectors can be used to store data related to peers and
  torrents inside a session type

- Add protocol::Metrics, conn::Metrics, and torrent::Metrics

  Metrics can be used to keep track of what data has been exchanged. The
  metrics may be used to change behavior between peers.

- Add PartialEq to protocol types

  For ReservedBytes and ReceivedHandshakeState

## [0.0.1] - 2022-04-19

### Added

- Initial release

[Unreleased]: https://github.com/bluk/gen_value/compare/v0.0.3...HEAD
[0.0.3]: https://github.com/bluk/gen_value/compare/v0.0.2...v0.0.3
[0.0.2]: https://github.com/bluk/gen_value/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/bluk/gen_value/releases/tag/v0.0.1