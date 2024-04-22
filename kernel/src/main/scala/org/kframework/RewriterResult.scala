// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework

import java.util.Optional

/**
 * Created by manasvi on 8/13/15.
 */
class RewriterResult(
    val rewriteSteps: Optional[Integer],
    val exitCode: Optional[Integer],
    val k: kore.K
) {}
