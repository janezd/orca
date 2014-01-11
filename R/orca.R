count4 <- function(edges) {
    edges <- t(data.matrix(edges))
    .C("count4",
       edges, dim(edges),
       orbits=matrix(0L, nrow=max(edges), ncol=15))$orbits
}

count5 <- function(edges) {
    edges <- t(data.matrix(edges))
    .C("count5",
       edges, dim(edges),
       orbits=matrix(0L, nrow=max(edges), ncol=73))$orbits
}

ecount4 <- function(edges) {
    edges <- t(data.matrix(edges))
    .C("ecount4",
       edges, dim(edges),
       orbits=matrix(0L, nrow=ncol(edges), ncol=12))$orbits
}

ecount5 <- function(edges) {
    edges <- t(data.matrix(edges))
    .C("ecount5",
       edges, dim(edges),
       orbits=matrix(0L, nrow=ncol(edges), ncol=68))$orbits
}
