#!/usr/bin/env bash
# Relink the two new Lean modules with the runtime from the accepted Stage 1 build.
set -euo pipefail
stage=.data/hinge-build
mkdir -p "$stage/assets"
archive="$stage/runtime.zip"
gh api /repos/"$GITHUB_REPOSITORY"/actions/artifacts/14199281733/zip > "$archive"
echo "b343cb5a0483c7a53085ba154b3b1ee5ae4442044a321186bf84180fd24cbe57  $archive" | sha256sum -c -
prefix=.data/live-portal-build/pass-1/files/.data/wasm-build/canonical
unzip -q "$archive" "$prefix/checker-core.a" "$prefix/runtime/include/*" "$prefix/runtime/lib/lean/libleanrt.a" "$prefix/runtime/libuv/src/libuv/libuv.a" -d "$stage"
core="$stage/$prefix"
git init -q "$stage/emsdk"
git -C "$stage/emsdk" fetch -q --depth=1 https://github.com/emscripten-core/emsdk.git a896e3d066448b3530dbcaa48869fafefd738f57
git -C "$stage/emsdk" checkout -q --detach FETCH_HEAD
"$stage/emsdk/emsdk" install 3.1.44
"$stage/emsdk/emsdk" activate 3.1.44
source "$stage/emsdk/emsdk_env.sh"
flags=(-O2 -flto -pthread -fwasm-exceptions -I "$core/runtime/include")
folder=diagram-assets
sources=(proofs/MemberDiagram.c qa/member-diagram/abi.c)
if [[ "${1:-}" == joint ]]; then
    folder=joint-diagram-assets
    sources=(proofs/HingeFrame{Checker,Wire}.c proofs/InclinedRelease{,Wire}.c proofs/FrameSpring{,Wire}.c
        proofs/MemberDiagram.c proofs/CardinalSpring.c proofs/JointMemberDiagram.c qa/joint-diagram/abi.c)
fi
if [[ "${1:-}" == inclined-diagram ]]; then
    folder=inclined-diagram-assets
    sources=(proofs/HingeFrameChecker.c proofs/InclinedRelease{,Wire}.c proofs/FrameSpring{,Wire}.c
        proofs/MemberDiagram.c proofs/InclinedDiagramStatics.c proofs/InclinedDiagram{,Wire}.c qa/inclined-diagram/abi.c)
fi
if [[ "${1:-}" == member-kinematics ]]; then
    folder=member-kinematics-assets
    sources=(proofs/HingeFrameChecker.c proofs/InclinedRelease{,Wire}.c proofs/FrameSpring{,Wire}.c
        proofs/MemberDiagram.c proofs/InclinedDiagramStatics.c proofs/InclinedDiagram{,Wire}.c
        proofs/MemberKinematics{,Wire}.c qa/member-kinematics/abi.c)
fi
if [[ "${1:-}" == ideal-truss ]]; then
    folder=ideal-truss-assets
    sources=(proofs/IdealTrussWire.c qa/ideal-truss/abi.c)
fi
if [[ "${1:-}" == week04-section ]]; then
    folder=week04-section-assets
    sources=(proofs/IdealTrussWire.c proofs/Week04SectionWire.c qa/week04-sections/abi.c)
fi
mkdir -p "$stage/$folder"
objects=()
for source in "${sources[@]}"; do
    object="$stage/$(basename "$source" .c).o"
    emcc "${flags[@]}" -c "$source" -o "$object"
    objects+=("$object")
done
em++ "${flags[@]}" -Wl,-u,ntohs --no-entry "${objects[@]}" -Wl,--start-group "$core/checker-core.a" \
    "$core/runtime/lib/lean/libleanrt.a" "$core/runtime/libuv/src/libuv/libuv.a" -Wl,--end-group \
    -sMODULARIZE=1 -sEXPORT_ES6=1 -sEXPORT_NAME=createChecker -sENVIRONMENT=web,worker \
    -sALLOW_MEMORY_GROWTH=1 -sINITIAL_MEMORY=33554432 -sMAXIMUM_MEMORY=134217728 \
    -sPTHREAD_POOL_SIZE=0 -sERROR_ON_UNDEFINED_SYMBOLS=1 \
    '-sEXPORTED_FUNCTIONS=["_checker_init","_checker_check","_input_ptr","_input_capacity","_output_ptr","_output_size","_output_capacity"]' \
    -o "$stage/$folder/checker.mjs"
node qa/member-diagram/prepare.mjs "$stage/$folder/"
